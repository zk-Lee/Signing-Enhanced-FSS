use crate::{
    ec_cycle_pcd::data_structures::{ECCyclePCDPK, ECCyclePCDVK, HelpCircuit, MainCircuit},
    Error, PCDPredicate, PCD,
};

use ark_crypto_primitives::{
    crh::{CRHScheme, constraints::CRHSchemeGadget, },
    crh::bowe_hopwood::CRH,
    crh::pedersen,
    snark::constraints::SNARKGadget,
    snark::FromFieldElementsGadget,
    snark::SNARK,
};
use ark_ec::{
    twisted_edwards::TECurveConfig,
    pairing::Pairing,
    CurveGroup
};
use ark_ff::{PrimeField, Field};
use ark_r1cs_std::{
    alloc::AllocVar, prelude::*, R1CSVar,
};
use ark_relations::r1cs::{
    ConstraintSystem, ConstraintSystemRef, OptimizationGoal,
};
use ark_std::{
    rand::{CryptoRng, Rng},
    boxed::Box,
    marker::PhantomData,
    vec::Vec
};
use ark_ff::BigInteger;
pub mod data_structures;

type BasePrimeField<E> = <<<E as Pairing>::G1 as CurveGroup>::BaseField as Field>::BasePrimeField;

pub trait ECCyclePCDConfig<MainEngine: Pairing, HelpEngine: Pairing> 
{
    type CRH: CRHScheme;
    type CRHGadget: CRHSchemeGadget<Self::CRH, MainEngine::ScalarField>;

    type MainSNARK: SNARK<MainEngine::ScalarField>;
    type HelpSNARK: SNARK<HelpEngine::ScalarField>;

    type MainSNARKGadget: SNARKGadget<
        MainEngine::ScalarField,
        BasePrimeField<MainEngine>,
        Self::MainSNARK
    >;
    type HelpSNARKGadget: SNARKGadget<
        HelpEngine::ScalarField,
        BasePrimeField<HelpEngine>,
        Self::HelpSNARK
    >;
}
pub struct ECCyclePCD<
    CC: TECurveConfig,
    WINDOW: pedersen::Window,
    MainEngine: Pairing,
    HelpEngine: Pairing,
    IC: ECCyclePCDConfig<MainEngine, HelpEngine>,
> {
    pub group_phantom: PhantomData<CC>,
    pub window_phantom: PhantomData<WINDOW>,
    pub main_engine_phantom: PhantomData<MainEngine>,
    pub help_engine_phantom: PhantomData<HelpEngine>,
    pub ivc_config: PhantomData<IC>,
}

impl<CC: TECurveConfig<BaseField = MainEngine::ScalarField>, WINDOW: pedersen::Window, MainEngine: Pairing<ScalarField = BasePrimeField<HelpEngine>>, HelpEngine: Pairing<ScalarField = BasePrimeField<MainEngine>>, IC: ECCyclePCDConfig<MainEngine, HelpEngine>>
    PCD<MainEngine::ScalarField> for ECCyclePCD<CC, WINDOW, MainEngine, HelpEngine, IC> {
    type ProvingKey = ECCyclePCDPK<CC, WINDOW, MainEngine, HelpEngine, IC>;
    type VerifyingKey = ECCyclePCDVK<CC, WINDOW, MainEngine, HelpEngine, IC>;
    type Proof = <IC::HelpSNARK as SNARK<HelpEngine::ScalarField>>::Proof;

    fn circuit_specific_setup<P: PCDPredicate<MainEngine::ScalarField>, R: Rng + CryptoRng>(
        predicate: &P,
        rng: &mut R,
    ) -> Result<(Self::ProvingKey, Self::VerifyingKey), Error> {
        let crh_pp = CRH::<CC, WINDOW>::setup(rng)?;

        let main_circuit = MainCircuit::<CC, WINDOW, MainEngine, HelpEngine, IC, P> {
            crh_pp: crh_pp.clone(),
            predicate: predicate.clone(),
            input_hash: None,
            help_vk: None,
            msg: vec![None; P::MSG_LEN],//Vec::with_capacity(P::MSG_LEN), //Vec::new(),
            prior_msgs: Vec::new(),
            prior_proofs: Vec::new(),
            base_case_bit: None,
        };
        let (main_pk, main_vk) = IC::MainSNARK::circuit_specific_setup(main_circuit, rng)?;

        let main_pvk = IC::MainSNARK::process_vk(&main_vk)?;

        let help_circuit = HelpCircuit::<MainEngine, HelpEngine, IC> {
            main_pvk: main_pvk.clone(),
            input_hash: None,
            main_proof: None,
        };
        let (help_pk, help_vk) = IC::HelpSNARK::circuit_specific_setup(help_circuit, rng)?;

        let pk = ECCyclePCDPK::<CC, WINDOW, MainEngine, HelpEngine, IC> {
            crh_pp: crh_pp.clone(),
            main_pk,
            help_pk,
            help_vk: help_vk.clone(),
            main_pvk,
        };
        let vk = ECCyclePCDVK::<CC, WINDOW, MainEngine, HelpEngine, IC> { crh_pp, help_vk };

        Ok((pk, vk))
    }

    fn prove<P: PCDPredicate<MainEngine::ScalarField>, R: Rng + CryptoRng>(
        pk: &ECCyclePCDPK<CC, WINDOW, MainEngine, HelpEngine, IC>,
        predicate: &P,
        msg: &[P::Message],
        prior_msgs: &[&[P::Message]],
        prior_proofs: &[Self::Proof],
        rng: &mut R,
    ) -> Result<Self::Proof, Error> {
        /*
         ** Compute the input hash.
         ** To avoid issues when the verifying key's native has different ToBytes compared with the gadgets',
         ** here we simulate the computation inside the gadget
         */
        let input_hash = {
            let tcs_sys = ConstraintSystem::<MainEngine::ScalarField>::new();
            let tcs = ConstraintSystemRef::new(tcs_sys);
            tcs.set_optimization_goal(OptimizationGoal::Weight);

            let help_vk_gadget = <IC::HelpSNARKGadget as SNARKGadget<
                HelpEngine::ScalarField,
                MainEngine::ScalarField,
                IC::HelpSNARK,
            >>::VerifyingKeyVar::new_witness(
                ark_relations::ns!(tcs, "vk"),
                || Ok(pk.help_vk.clone()),
            )?;

            let mut msg_gadgets = Vec::new();
            for m in msg.iter() {
                msg_gadgets.push(P::MessageVar::new_witness(
                    ark_relations::ns!(tcs, "msg"),
                    || Ok(m),
                )?);
            }

            let help_vk_bytes_gadget = help_vk_gadget.to_bytes()?;
            let mut committed_vk = Vec::<u8>::new();

            for byte in &help_vk_bytes_gadget {
                committed_vk.push(byte.value().unwrap_or_default());
            }
            let vk_hash = CRH::<CC, WINDOW>::evaluate(&pk.crh_pp, committed_vk)?;
/* 1. REMOVED
            //let vk_hash_bytes = to_bytes!(vk_hash)?;
*/
/* 2. SLIGHTLY DIFFIERENT
            //let mut bytes = to_bytes![biginteger].unwrap();
            let vk_hash_bytes = {
                let mut result = vec![0u8; vk_hash.serialized_size(Compress::No)];
                vk_hash
                    .serialize_compressed(&mut Cursor::new(&mut result[..]))
                    .unwrap();
                result
            };
*/
/* FINAL */
            let vk_hash_bytes = vk_hash.into_bigint().to_bytes_le();
//println!("vk_hash[Not Circuit]: {:?}", vk_hash);                    //JH
//println!("vk_hash_bytes[Not Circuit]: {:?}", vk_hash_bytes);        //JH

            //let msg_bytes_gadget = msg_gadgets.to_bytes()?;

            let mut committed_input = Vec::<u8>::new();
            for byte in vk_hash_bytes.iter() {
                committed_input.push(*byte);
            }
            for i in 0..P::MSG_LEN {
                let msg_bytes_gadget = msg_gadgets[i].to_bytes()?;
                for byte in &msg_bytes_gadget {
                    committed_input.push(byte.value().unwrap_or_default());
                }
            }
            CRH::<CC, WINDOW>::evaluate(&pk.crh_pp, committed_input)?
        };
        
//println!("input_hash[Not Circuit]: {:?}", input_hash);        //JH

        let main_circuit: MainCircuit<CC, WINDOW, MainEngine, HelpEngine, IC, P>;
        if prior_msgs.is_empty() {
            main_circuit = MainCircuit::<CC, WINDOW, MainEngine, HelpEngine, IC, P> {
                crh_pp: pk.crh_pp.clone(),
                predicate: (*predicate).clone(),
                input_hash: Some(input_hash.clone()),
                help_vk: Some(pk.help_vk.clone()),
                msg: msg.iter().map(|m| Some(m.clone())).collect(),//msg.to_vec(),//Some(msg.clone()),
                prior_msgs: Vec::new(),
                prior_proofs: Vec::new(),
                base_case_bit: Some(true),
            };
        } else {
            main_circuit = MainCircuit::<CC, WINDOW, MainEngine, HelpEngine, IC, P> {
                crh_pp: pk.crh_pp.clone(),
                predicate: (*predicate).clone(),
                input_hash: Some(input_hash.clone()),
                help_vk: Some(pk.help_vk.clone()),//JH remove clone
                msg: msg.iter().map(|m| Some(m.clone())).collect(),//msg.to_vec(),//Some(msg.clone()),
                prior_msgs: prior_msgs.iter().map(|pm| pm.to_vec()).collect(),
                prior_proofs: prior_proofs.to_vec(),
                base_case_bit: Some(false),
            };
        }

        let main_proof = IC::MainSNARK::prove(&pk.main_pk, main_circuit, rng)?;

        let help_circuit = HelpCircuit::<MainEngine, HelpEngine, IC> {
            main_pvk: pk.main_pvk.clone(),
            input_hash: Some(input_hash),
            main_proof: Some(main_proof),
        };

        let help_proof = IC::HelpSNARK::prove(&pk.help_pk, help_circuit, rng)?;

        Ok(help_proof)
    }

    fn verify<P: PCDPredicate<MainEngine::ScalarField>>(
        vk: &Self::VerifyingKey,
        msg: &[P::Message],
        proof: &Self::Proof,
    ) -> Result<bool, Error> {
        /*
         ** Compute the input hash.
         ** To avoid issues when the verifying key's native has different ToBytes compared with the gadgets',
         ** here we simulate the computation inside the gadget
         */
        let input_hash = {
            let tcs_sys = ConstraintSystem::<MainEngine::ScalarField>::new();
            let tcs = ConstraintSystemRef::new(tcs_sys);
            tcs.set_optimization_goal(OptimizationGoal::Weight);

            let help_vk_gadget = <IC::HelpSNARKGadget as SNARKGadget<
                HelpEngine::ScalarField,
                MainEngine::ScalarField,
                IC::HelpSNARK,
            >>::VerifyingKeyVar::new_witness(
                ark_relations::ns!(tcs, "vk"),
                || Ok(vk.help_vk.clone()),
            )?;

            let mut msg_gadgets = Vec::new();
            for m in msg.iter() {
                msg_gadgets.push(P::MessageVar::new_witness(
                    ark_relations::ns!(tcs, "alloc_z"),
                    || Ok(m),
                )?);
            }

            let help_vk_bytes_gadget = help_vk_gadget.to_bytes()?;
            let mut committed_vk = Vec::<u8>::new();
            for byte in &help_vk_bytes_gadget {
                committed_vk.push(byte.value().unwrap_or_default());
            }
            let vk_hash = CRH::<CC, WINDOW>::evaluate(&vk.crh_pp, committed_vk)?;
            let vk_hash_bytes = vk_hash.into_bigint().to_bytes_le();

            //let msg_bytes_gadget = msg_gadgets.to_bytes()?;

            let mut committed_input = Vec::<u8>::new();
            for byte in vk_hash_bytes.iter() {
                committed_input.push(*byte);
            }
            for i in 0..P::MSG_LEN {
                let msg_bytes_gadget = msg_gadgets[i].to_bytes()?;
                for byte in &msg_bytes_gadget {
                    committed_input.push(byte.value().unwrap_or_default());
                }
            }

            CRH::<CC, WINDOW>::evaluate(&vk.crh_pp, committed_input)?
        };

        let main_public_input = vec![input_hash];

        let help_public_input = <IC::MainSNARKGadget as SNARKGadget<
            MainEngine::ScalarField,
            BasePrimeField<MainEngine>,
            IC::MainSNARK,
        >>::InputVar::repack_input(&main_public_input);

        let verify_result = IC::HelpSNARK::verify(&vk.help_vk, &help_public_input, &proof);

        match verify_result {
            Ok(res) => Ok(res),
            Err(err) => Err(Box::new(err)),
        }
    }
}