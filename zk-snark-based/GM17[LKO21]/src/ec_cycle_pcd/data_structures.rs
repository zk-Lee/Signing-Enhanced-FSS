use crate::{
    ec_cycle_pcd::ECCyclePCDConfig,
    PCDPredicate, Terminal_PCDPredicate,
};
use ark_crypto_primitives::{
    crh::{CRHScheme, constraints::CRHSchemeGadget, },
    crh::bowe_hopwood::{CRH, constraints::CRHGadget, },
    crh::pedersen,
    snark::{FromFieldElementsGadget, SNARKGadget, SNARK},
};
use ark_ec::{
    twisted_edwards::TECurveConfig,
    pairing::Pairing,
    CurveGroup
};
use ark_ff::{PrimeField, Field};
use ark_r1cs_std::{
    alloc::AllocVar, bits::boolean::Boolean, bits::uint8::UInt8, fields::fp::FpVar, prelude::*,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_std::{
    vec::Vec,
    rand::SeedableRng,
};
type BasePrimeField<E> = <<<E as Pairing>::G1 as CurveGroup>::BaseField as Field>::BasePrimeField;

use ark_serialize::CanonicalSerialize;
#[derive(CanonicalSerialize)]
pub struct ECCyclePCDPK<
    CC: TECurveConfig,
    WINDOW: pedersen::Window,
    MainEngine: Pairing,
    HelpEngine: Pairing,
    IC: ECCyclePCDConfig<MainEngine, HelpEngine>,
> {
    pub crh_pp: <CRH<CC, WINDOW> as CRHScheme>::Parameters,
    pub main_pk: <IC::MainSNARK as SNARK<MainEngine::ScalarField>>::ProvingKey,
    pub main_pvk: <IC::MainSNARK as SNARK<MainEngine::ScalarField>>::ProcessedVerifyingKey,
    pub help_pk: <IC::HelpSNARK as SNARK<HelpEngine::ScalarField>>::ProvingKey,
    pub help_vk: <IC::HelpSNARK as SNARK<HelpEngine::ScalarField>>::VerifyingKey,
}

impl<CC: TECurveConfig, WINDOW: pedersen::Window, MainEngine: Pairing<ScalarField = BasePrimeField<HelpEngine>>, HelpEngine: Pairing<ScalarField = BasePrimeField<MainEngine>>, IC: ECCyclePCDConfig<MainEngine, HelpEngine>> Clone
    for ECCyclePCDPK<CC, WINDOW, MainEngine, HelpEngine, IC>
{
    fn clone(&self) -> Self {
        Self {
            crh_pp: self.crh_pp.clone(),
            main_pk: self.main_pk.clone(),
            main_pvk: self.main_pvk.clone(),
            help_pk: self.help_pk.clone(),
            help_vk: self.help_vk.clone(),
        }
    }
}

#[derive(CanonicalSerialize)]
pub struct ECCyclePCDVK<
    CC: TECurveConfig,
    WINDOW: pedersen::Window,
    MainEngine: Pairing,
    HelpEngine: Pairing,
    IC: ECCyclePCDConfig<MainEngine, HelpEngine>,
> {
    pub crh_pp: <CRH<CC, WINDOW> as CRHScheme>::Parameters,
    pub help_vk: <IC::HelpSNARK as SNARK<HelpEngine::ScalarField>>::VerifyingKey,
}

impl<CC: TECurveConfig, WINDOW: pedersen::Window, MainEngine: Pairing<ScalarField = BasePrimeField<HelpEngine>>, HelpEngine: Pairing<ScalarField = BasePrimeField<MainEngine>>, IC: ECCyclePCDConfig<MainEngine, HelpEngine>> Clone
    for ECCyclePCDVK<CC, WINDOW, MainEngine, HelpEngine, IC>
{
    fn clone(&self) -> Self {
        Self {
            crh_pp: self.crh_pp.clone(),
            help_vk: self.help_vk.clone(),
        }
    }
}

pub struct DefaultCircuit {
    pub public_input_size: usize,
}

impl Clone for DefaultCircuit {
    fn clone(&self) -> Self {
        Self {
            public_input_size: self.public_input_size,
        }
    }
}

impl Copy for DefaultCircuit {}

impl<F: PrimeField> ConstraintSynthesizer<F> for DefaultCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        for _ in 0..self.public_input_size {
            let gadget = FpVar::<F>::new_input(ark_relations::ns!(cs, "alloc"), || Ok(F::one()))?;
            gadget.to_bits_le()?;
        }

        Ok(())
    }
}

pub struct MainCircuit<
    CC: TECurveConfig,
    WINDOW: pedersen::Window, 
    MainEngine: Pairing,
    HelpEngine: Pairing,
    IC: ECCyclePCDConfig<MainEngine, HelpEngine>,
    P: PCDPredicate<MainEngine::ScalarField>,
> {
    pub crh_pp: <CRH<CC, WINDOW> as CRHScheme>::Parameters,
    pub predicate: P,
    pub input_hash: Option<<CRH<CC, WINDOW> as CRHScheme>::Output>, //Option<MainField>, //Option<<IC::CRH as CRHScheme>::Output>,
    pub help_vk: Option<<IC::HelpSNARK as SNARK<HelpEngine::ScalarField>>::VerifyingKey>,
    pub msg: Vec<Option<P::Message>>,
    pub prior_msgs: Vec<Vec<P::Message>>,
    pub prior_proofs: Vec<<IC::HelpSNARK as SNARK<HelpEngine::ScalarField>>::Proof>,
    pub base_case_bit: Option<bool>,
}

impl<
        CC: TECurveConfig<BaseField = MainEngine::ScalarField>,
        WINDOW: pedersen::Window, 
        MainEngine: Pairing<ScalarField = BasePrimeField<HelpEngine>>,
        HelpEngine: Pairing<ScalarField = BasePrimeField<MainEngine>>,
        IC: ECCyclePCDConfig<MainEngine, HelpEngine>,
        P: PCDPredicate<MainEngine::ScalarField>,
    > ConstraintSynthesizer<MainEngine::ScalarField> for MainCircuit<CC, WINDOW, MainEngine, HelpEngine, IC, P> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<MainEngine::ScalarField>,
    ) -> Result<(), SynthesisError> {
        assert!(self.base_case_bit != Some(false) || self.prior_msgs.len() == P::PRIOR_PROOF_NUM);
        assert!(self.base_case_bit != Some(false) || self.prior_proofs.len() == P::PRIOR_PROOF_NUM);

        /*
         * allocation
         */
        let input_hash_gadget =
            <CRHGadget<CC, FpVar<MainEngine::ScalarField>> as CRHSchemeGadget<CRH<CC, WINDOW>, <CC::BaseField as Field>::BasePrimeField>>::OutputVar::new_input(
                ark_relations::ns!(cs, "alloc#x"),
                || Ok(self.input_hash.clone().unwrap_or_default()),
            )?;

        let main_public_input = vec![self.input_hash.unwrap_or_default()];

        let help_public_input = <IC::MainSNARKGadget as SNARKGadget<
            MainEngine::ScalarField,
            BasePrimeField<MainEngine>,
            IC::MainSNARK,
        >>::InputVar::repack_input(&main_public_input);

        let default_circ = DefaultCircuit {
            public_input_size: help_public_input.len(),
        };
        let mut default_rng = &mut ark_std::rand::rngs::StdRng::seed_from_u64(0u64);
        let (default_pk, default_vk) = IC::HelpSNARK::circuit_specific_setup(default_circ, &mut default_rng).unwrap();
        let default_proof = <IC::HelpSNARK as SNARK<HelpEngine::ScalarField>>::prove(&default_pk, default_circ, &mut default_rng).unwrap();

        let crh_pp_gadget = <CRHGadget<CC, FpVar<MainEngine::ScalarField>> as CRHSchemeGadget<CRH<CC, WINDOW>, <CC::BaseField as Field>::BasePrimeField>>::ParametersVar::new_constant(
            ark_relations::ns!(cs,  "alloc_crh_for_cycle_ivc"),
            self.crh_pp.clone(),
        )?;

        let help_vk = self.help_vk.unwrap_or(default_vk);
        let help_vk_gadget = <IC::HelpSNARKGadget as SNARKGadget<
            HelpEngine::ScalarField,
            BasePrimeField<HelpEngine>,
            IC::HelpSNARK,
        >>::new_verification_key_unchecked(
            ark_relations::ns!(cs, "alloc#vk"),
            || Ok(help_vk),
            AllocationMode::Witness,
        )?;

        
        assert!(self.msg.len() == P::MSG_LEN);
        let mut msg_gadgets = Vec::new();
        for i in 0..P::MSG_LEN {
            let m = self.msg[i].clone().unwrap_or_default();
            msg_gadgets.push(P::MessageVar::new_witness(
                ark_relations::ns!(cs, "alloc_z"),
                || Ok(m),
            )?);
        }

        let mut prior_msg_gadgetss = Vec::new();
        if self.base_case_bit != Some(false) {
            let default_msg = P::Message::default();
            for _ in 0..P::PRIOR_PROOF_NUM {
                let mut prior_msg_gadgets = Vec::new();
                for _ in 0..P::MSG_LEN {
                    prior_msg_gadgets.push(P::MessageVar::new_witness(
                        ark_relations::ns!(cs, "alloc_z_in"),
                        || Ok(default_msg.clone()),
                    )?);
                }
                prior_msg_gadgetss.push(prior_msg_gadgets);
            }
        } else {
            for prior_msg in self.prior_msgs.iter() {
                let mut prior_msg_gadgets = Vec::new();
                for prior_m in prior_msg.iter() {
                    prior_msg_gadgets.push(P::MessageVar::new_witness(
                        ark_relations::ns!(cs, "alloc_z_in"),
                        || Ok(prior_m),
                    )?);
                }
                prior_msg_gadgetss.push(prior_msg_gadgets);
            }
        }

        let mut prior_proof_gadgets = Vec::new();
        if self.base_case_bit != Some(false) {
            for _ in 0..P::PRIOR_PROOF_NUM {
                prior_proof_gadgets.push(<IC::HelpSNARKGadget as SNARKGadget<
                    HelpEngine::ScalarField,
                    BasePrimeField<HelpEngine>,
                    IC::HelpSNARK,
                >>::ProofVar::new_witness(
                    ark_relations::ns!(cs, "alloc_prior_proof"),
                    || Ok(default_proof.clone()),
                )?);
            }
        } else {
            for prior_proof in self.prior_proofs.iter() {
                prior_proof_gadgets.push(<IC::HelpSNARKGadget as SNARKGadget<
                    HelpEngine::ScalarField,
                    BasePrimeField<HelpEngine>,
                    IC::HelpSNARK,
                >>::ProofVar::new_witness(
                    ark_relations::ns!(cs, "alloc_prior_proof"),
                    || Ok(prior_proof),
                )?);
            }
        }

        let base_case_bit = self.base_case_bit.unwrap_or_default();
        let b_base_gadget = Boolean::new_witness(ark_relations::ns!(cs, "alloc_b_base"), || Ok(base_case_bit))?;

        /*
         * compute vk hash
         */

        let help_vk_bytes_gadget = help_vk_gadget.to_bytes()?;

        let mut committed_vk = Vec::<UInt8<MainEngine::ScalarField>>::new();
        for byte in &help_vk_bytes_gadget {
            committed_vk.push(byte.clone());
        }

        let vk_hash_gadget = <CRHGadget<CC, FpVar<MainEngine::ScalarField>> as CRHSchemeGadget<CRH<CC, WINDOW>, <CC::BaseField as Field>::BasePrimeField>>::evaluate(&crh_pp_gadget, &committed_vk)?;

        let vk_hash_bytes_gadget = vk_hash_gadget.to_bytes()?;

        /*
         * check input
         */

        //let msg_bytes_gadget = msg_gadgets.to_bytes()?;

        let mut committed_input = Vec::<UInt8<MainEngine::ScalarField>>::new();
        for byte in &vk_hash_bytes_gadget {
            committed_input.push(byte.clone());
        }
        for i in 0..P::MSG_LEN {
            let msg_bytes_gadget = msg_gadgets[i].to_bytes()?;
            for byte in &msg_bytes_gadget {
                committed_input.push(byte.clone());
            }
        }
        let input_hash_supposed_gadget = <CRHGadget<CC, FpVar<MainEngine::ScalarField>> as CRHSchemeGadget<CRH<CC, WINDOW>, <CC::BaseField as Field>::BasePrimeField>>::evaluate(&crh_pp_gadget, &committed_input)?;

/*
        println!("main_public_input: {:?}", main_public_input);
        println!("help_public_input: {:?}", help_public_input);
        //println!("help_vk: {:?}", help_vk);           //error
        //println!("msg: {:?}", msg);                   //error
        println!("base_case_bit: {:?}", base_case_bit);
        //println!("committed_vk: {:?}", committed_vk.value());                 //value() //TL;DR
        //println!("committed_input: {:?}", committed_input.value());           //value() //TL;DR

        println!("vk_hash_gadget: {:?}", vk_hash_gadget.value());                           //value() //TL;DR
        println!("help_vk_bytes_gadget: {:?}", help_vk_bytes_gadget.value());               //value()

        println!("input_hash_gadget: {:?}", input_hash_gadget.value());                     //value()
        println!("input_hash_supposed_gadget: {:?}", input_hash_supposed_gadget.value());   //value()
*/
        input_hash_supposed_gadget.enforce_equal(&input_hash_gadget)?;  

        /*
         * check the predicate
         */

        self.predicate.generate_constraints(
            ark_relations::ns!(cs, "check_predicate").cs(),
            &msg_gadgets,
            prior_msg_gadgetss.iter().map(|vec| vec.as_slice()).collect::<Vec<_>>().as_slice(),
            &b_base_gadget,
        )?;

        /*
         * check each prior proof
         */

        let mut prior_proofs_verified = Boolean::Constant(true);

        for (prior_msg_gadgets, prior_proof_gadget) in
            prior_msg_gadgetss.iter().zip(prior_proof_gadgets.iter())
        {
            //let prior_msg_bytes_gadget = prior_msg_gadgets.to_bytes()?;

            let mut committed_prior_input = Vec::<UInt8<MainEngine::ScalarField>>::new();
            for byte in vk_hash_bytes_gadget.iter() {
                committed_prior_input.push(byte.clone());
            }
            for i in 0..P::MSG_LEN {
                let prior_msg_bytes_gadget = prior_msg_gadgets[i].to_bytes()?;
                for byte in &prior_msg_bytes_gadget {
                    committed_prior_input.push(byte.clone());
                }
            }
            let prior_input_hash_gadget = <CRHGadget<CC, FpVar<MainEngine::ScalarField>> as CRHSchemeGadget<CRH<CC, WINDOW>, <CC::BaseField as Field>::BasePrimeField>>::evaluate(&crh_pp_gadget, &committed_prior_input)?;

            let prior_input_hash_gadget_field_gadgets = vec![prior_input_hash_gadget];

            let prior_input_hash_converted_gadget = <IC::HelpSNARKGadget as SNARKGadget<
                HelpEngine::ScalarField,
                BasePrimeField<HelpEngine>,
                IC::HelpSNARK,
            >>::InputVar::from_field_elements(
                &prior_input_hash_gadget_field_gadgets
            )?;

            let verification_result =
                <IC::HelpSNARKGadget as SNARKGadget<HelpEngine::ScalarField, MainEngine::ScalarField, IC::HelpSNARK>>::verify(
                    &help_vk_gadget,
                    &prior_input_hash_converted_gadget,
                    &prior_proof_gadget,
                )?;

            prior_proofs_verified = prior_proofs_verified.and(&verification_result)?;
        }

        b_base_gadget
            .or(&prior_proofs_verified)?
            .enforce_equal(&Boolean::constant(true))?;

        Ok(())
    }
}

pub struct HelpCircuit<
    MainEngine: Pairing,
    HelpEngine: Pairing,
    IC: ECCyclePCDConfig<MainEngine, HelpEngine>,
> {
    pub main_pvk: <IC::MainSNARK as SNARK<MainEngine::ScalarField>>::ProcessedVerifyingKey,

    pub input_hash: Option<MainEngine::ScalarField>, ////////////Option<<IC::CRH as CRHScheme>::Output>,
    pub main_proof: Option<<IC::MainSNARK as SNARK<MainEngine::ScalarField>>::Proof>,
}

impl<MainEngine: Pairing<ScalarField = BasePrimeField<HelpEngine>>, HelpEngine: Pairing<ScalarField = BasePrimeField<MainEngine>>, IC: ECCyclePCDConfig<MainEngine, HelpEngine>>
    ConstraintSynthesizer<HelpEngine::ScalarField> for HelpCircuit<MainEngine, HelpEngine, IC> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<HelpEngine::ScalarField>,
    ) -> Result<(), SynthesisError> {
        let input_hash = self.input_hash.unwrap_or_default();

        let main_public_input = vec![input_hash];

        let main_public_input_num_of_field_elements = main_public_input.len();

        let default_circ = DefaultCircuit {
            public_input_size: main_public_input_num_of_field_elements,
        };
        let mut default_rng = &mut ark_std::rand::rngs::StdRng::seed_from_u64(0u64);
        let (default_pk, _) = <IC::MainSNARK as SNARK<MainEngine::ScalarField>>::circuit_specific_setup(
            default_circ,
            &mut default_rng,
        )
        .unwrap();
        let default_proof =
            <IC::MainSNARK as SNARK<MainEngine::ScalarField>>::prove(&default_pk, default_circ, &mut default_rng)
                .unwrap();

        let main_proof = self.main_proof.unwrap_or(default_proof);

        let input_hash_gadget = <IC::MainSNARKGadget as SNARKGadget<
            MainEngine::ScalarField,
            BasePrimeField<MainEngine>,
            IC::MainSNARK,
        >>::InputVar::new_input(
            ark_relations::ns!(cs, "verifier"),
            || Ok(main_public_input),
        )?;

        let main_pvk_gadget = <IC::MainSNARKGadget as SNARKGadget<
            MainEngine::ScalarField,
            BasePrimeField<MainEngine>,
            IC::MainSNARK,
        >>::ProcessedVerifyingKeyVar::new_constant(
            ark_relations::ns!(cs, "alloc_pvk"),
            self.main_pvk,
        )?;

        let main_proof_gadget = <IC::MainSNARKGadget as SNARKGadget<
            MainEngine::ScalarField,
            BasePrimeField<MainEngine>,
            IC::MainSNARK,
        >>::ProofVar::new_witness(
            ark_relations::ns!(cs, "alloc_pi_alpha"), || Ok(main_proof)
        )?;

        <IC::MainSNARKGadget as SNARKGadget<
            MainEngine::ScalarField,
            BasePrimeField<MainEngine>,
            IC::MainSNARK,
        >>::verify_with_processed_vk(
            &main_pvk_gadget,
            &input_hash_gadget,
            &main_proof_gadget,
        )?.enforce_equal(&Boolean::Constant(true))?;

        Ok(())
    }
}































#[derive(CanonicalSerialize)]
pub struct Terminal_ECCyclePCDPK<
    CC: TECurveConfig,
    WINDOW: pedersen::Window,
    MainEngine: Pairing,
    HelpEngine: Pairing,
    IC: ECCyclePCDConfig<MainEngine, HelpEngine>,
> {
    pub crh_pp: <CRH<CC, WINDOW> as CRHScheme>::Parameters,
    pub main_pk: <IC::MainSNARK as SNARK<MainEngine::ScalarField>>::ProvingKey,
    pub help_vk: <IC::HelpSNARK as SNARK<HelpEngine::ScalarField>>::VerifyingKey,
}

impl<CC: TECurveConfig, WINDOW: pedersen::Window, MainEngine: Pairing<ScalarField = BasePrimeField<HelpEngine>>, HelpEngine: Pairing<ScalarField = BasePrimeField<MainEngine>>, IC: ECCyclePCDConfig<MainEngine, HelpEngine>> Clone
    for Terminal_ECCyclePCDPK<CC, WINDOW, MainEngine, HelpEngine, IC>
{
    fn clone(&self) -> Self {
        Self {
            crh_pp: self.crh_pp.clone(),
            main_pk: self.main_pk.clone(),
            help_vk: self.help_vk.clone(),
        }
    }
}

#[derive(CanonicalSerialize)]
pub struct Terminal_ECCyclePCDVK<
    MainEngine: Pairing,
    HelpEngine: Pairing,
    IC: ECCyclePCDConfig<MainEngine, HelpEngine>,
> {
    pub main_pvk: <IC::MainSNARK as SNARK<MainEngine::ScalarField>>::ProcessedVerifyingKey,
}

impl<MainEngine: Pairing<ScalarField = BasePrimeField<HelpEngine>>, HelpEngine: Pairing<ScalarField = BasePrimeField<MainEngine>>, IC: ECCyclePCDConfig<MainEngine, HelpEngine>> Clone
    for Terminal_ECCyclePCDVK<MainEngine, HelpEngine, IC>
{
    fn clone(&self) -> Self {
        Self {
            main_pvk: self.main_pvk.clone(),
        }
    }
}




pub struct Terminal_MainCircuit<
    CC: TECurveConfig,
    WINDOW: pedersen::Window, 
    MainEngine: Pairing,
    HelpEngine: Pairing,
    IC: ECCyclePCDConfig<MainEngine, HelpEngine>,
    P: Terminal_PCDPredicate<MainEngine::ScalarField>,
> {
    pub crh_pp: <CRH<CC, WINDOW> as CRHScheme>::Parameters,
    pub predicate: P,
    pub help_vk: Option<<IC::HelpSNARK as SNARK<HelpEngine::ScalarField>>::VerifyingKey>,
    pub msg: Vec<Option<P::Message>>,
    pub prior_msgs: Vec<Vec<P::Message>>,
    pub prior_proofs: Vec<<IC::HelpSNARK as SNARK<HelpEngine::ScalarField>>::Proof>,
}

impl<   CC: TECurveConfig<BaseField = MainEngine::ScalarField>,
        WINDOW: pedersen::Window, 
        MainEngine: Pairing<ScalarField = BasePrimeField<HelpEngine>>,
        HelpEngine: Pairing<ScalarField = BasePrimeField<MainEngine>>,
        IC: ECCyclePCDConfig<MainEngine, HelpEngine>,
        P: Terminal_PCDPredicate<MainEngine::ScalarField>,
    > ConstraintSynthesizer<MainEngine::ScalarField> for Terminal_MainCircuit<CC, WINDOW, MainEngine, HelpEngine, IC, P> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<MainEngine::ScalarField>,
    ) -> Result<(), SynthesisError> {
        assert!(self.prior_msgs.len() == P::PRIOR_PROOF_NUM);
        assert!(self.prior_proofs.len() == P::PRIOR_PROOF_NUM);

        let crh_pp_gadget = <CRHGadget<CC, FpVar<MainEngine::ScalarField>> as CRHSchemeGadget<CRH<CC, WINDOW>, <CC::BaseField as Field>::BasePrimeField>>::ParametersVar::new_constant(
            ark_relations::ns!(cs,  "alloc_crh_for_cycle_ivc"),
            self.crh_pp.clone(),
        )?;

        let help_vk = self.help_vk.unwrap();
        let help_vk_gadget = <IC::HelpSNARKGadget as SNARKGadget<
            HelpEngine::ScalarField,
            BasePrimeField<HelpEngine>,
            IC::HelpSNARK,
        >>::new_verification_key_unchecked(
            ark_relations::ns!(cs, "alloc#vk"),
            || Ok(help_vk),
            AllocationMode::Witness,    //AllocationMode::Input
        )?;

        assert!(self.msg.len() == P::MSG_LEN);
        let mut msg_gadgets = Vec::new();
        for i in 0..P::MSG_LEN {
            let m = self.msg[i].clone().unwrap_or_default();
            msg_gadgets.push(P::MessageVar::new_input(ark_relations::ns!(cs, "alloc_z"), || Ok(m),)?);        //new_witness
        }

        let mut prior_msg_gadgetss = Vec::new();
        for prior_msg in self.prior_msgs.iter() {
            let mut prior_msg_gadgets = Vec::new();
            for prior_m_value in prior_msg.iter() {
                prior_msg_gadgets.push(P::MessageVar::new_witness(ark_relations::ns!(cs, "alloc_z_in"), || Ok(prior_m_value),)?);
            }
            prior_msg_gadgetss.push(prior_msg_gadgets);
        }

        let mut prior_proof_gadgets = Vec::new();
        for prior_proof in self.prior_proofs.iter() {
            prior_proof_gadgets.push(<IC::HelpSNARKGadget as SNARKGadget<
                HelpEngine::ScalarField,
                BasePrimeField<HelpEngine>,
                IC::HelpSNARK,
            >>::ProofVar::new_witness(ark_relations::ns!(cs, "alloc_prior_proof"), || Ok(prior_proof),)?);
        }

        /*
         * check the predicate
         */

        self.predicate.generate_constraints(
            ark_relations::ns!(cs, "check_predicate").cs(),
            &msg_gadgets,
            prior_msg_gadgetss.iter().map(|vec| vec.as_slice()).collect::<Vec<_>>().as_slice(),
        )?;

        /*
         * check each prior proof
         */


        let help_vk_bytes_gadget = help_vk_gadget.to_bytes()?;

        let mut committed_vk = Vec::<UInt8<MainEngine::ScalarField>>::new();
        for byte in &help_vk_bytes_gadget {
            committed_vk.push(byte.clone());
        }

        let vk_hash_gadget = <CRHGadget<CC, FpVar<MainEngine::ScalarField>> as CRHSchemeGadget<CRH<CC, WINDOW>, <CC::BaseField as Field>::BasePrimeField>>::evaluate(&crh_pp_gadget, &committed_vk)?;

        let vk_hash_bytes_gadget = vk_hash_gadget.to_bytes()?;



        let mut prior_proofs_verified = Boolean::Constant(true);

        for (prior_msg_gadgets, prior_proof_gadget) in
            prior_msg_gadgetss.iter().zip(prior_proof_gadgets.iter())
        {
            //let prior_msg_bytes_gadget = prior_msg_gadgets.to_bytes()?;

            let mut committed_prior_input = Vec::<UInt8<MainEngine::ScalarField>>::new();
            for byte in vk_hash_bytes_gadget.iter() {
                committed_prior_input.push(byte.clone());
            }
            for i in 0..P::PRIOR_MSG_LEN {
                let prior_msg_bytes_gadget = prior_msg_gadgets[i].to_bytes()?;
                for byte in &prior_msg_bytes_gadget {
                    committed_prior_input.push(byte.clone());
                }
            }
            let prior_input_hash_gadget = <CRHGadget<CC, FpVar<MainEngine::ScalarField>> as CRHSchemeGadget<CRH<CC, WINDOW>, <CC::BaseField as Field>::BasePrimeField>>::evaluate(&crh_pp_gadget, &committed_prior_input)?;

            let prior_input_hash_gadget_field_gadgets = vec![prior_input_hash_gadget];

            let prior_input_hash_converted_gadget = <IC::HelpSNARKGadget as SNARKGadget<
                HelpEngine::ScalarField,
                BasePrimeField<HelpEngine>,
                IC::HelpSNARK,
            >>::InputVar::from_field_elements(
                &prior_input_hash_gadget_field_gadgets
            )?;

            let verification_result =
                <IC::HelpSNARKGadget as SNARKGadget<HelpEngine::ScalarField, MainEngine::ScalarField, IC::HelpSNARK>>::verify(
                    &help_vk_gadget,
                    &prior_input_hash_converted_gadget,
                    &prior_proof_gadget,
                )?;

            prior_proofs_verified = prior_proofs_verified.and(&verification_result)?;
        }

        prior_proofs_verified.enforce_equal(&Boolean::constant(true))?;

        Ok(())
    }
}