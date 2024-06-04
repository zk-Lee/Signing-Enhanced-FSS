//cargo run --example FSSN
#![allow(clippy::op_ref, clippy::type_complexity)]

use ark_serialize::CanonicalSerialize;

use ark_ff::PrimeField;
use ark_gm17::{constraints::GM17VerifierGadget, GM17};
/*
//use ark_mnt4_753::constraints::FqVar;
use ark_ed_on_mnt4_753::EdwardsConfig;
use ark_mnt4_753::constraints::PairingVar as MNT4PairingVar;
use ark_mnt4_753::{MNT4_753 as MNT4};
use ark_mnt6_753::constraints::PairingVar as MNT6PairingVar;
use ark_mnt6_753::MNT6_753 as MNT6;
pub const NW: usize = 112;
*/
//use ark_mnt4_298::constraints::FqVar;
//use ark_mnt4_298::{Fq, Fr, MNT4_298 as MNT4};
//
use ark_ed_on_mnt4_298::EdwardsConfig;
use ark_mnt4_298::constraints::PairingVar as MNT4PairingVar;
use ark_mnt4_298::{MNT4_298 as MNT4};
use ark_mnt6_298::constraints::PairingVar as MNT6PairingVar;
use ark_mnt6_298::MNT6_298 as MNT6;
pub const NW: usize = 48;
//

use ark_ec::pairing::Pairing;
use ark_pcd::ec_cycle_pcd::{ECCyclePCD, ECCyclePCDConfig};

use ark_crypto_primitives::{
    crh::bowe_hopwood::{CRH, constraints::CRHGadget, },
    crh::pedersen,

    crh::{CRHScheme, CRHSchemeGadget},
    crh::poseidon::{
        CRH as PCRH,
        constraints::{CRHGadget as PCRHGadget, CRHParametersVar as PCRHParametersVar},
    },
    sponge::{
        poseidon::PoseidonConfig,//{PoseidonConfig, PoseidonSponge},
        Absorb,
    },
};
use ark_pcd::{PCDPredicate, PCD};
use ark_r1cs_std::{
    bits::boolean::Boolean,
    eq::EqGadget,
    fields::fp::FpVar,
    alloc::AllocVar,
    fields::fp::AllocatedFp,
};
use std::ops::Add;

use ark_relations::{
    //lc, ns,
    //r1cs::{ConstraintSystemRef, SynthesisError, Variable},
    r1cs::{ConstraintSystemRef, SynthesisError},
};
use ark_std::{
    test_rng, UniformRand,
    rand::{RngCore, SeedableRng},
};
use std::time::Instant;
#[derive(Clone)]
pub struct TestWindow {}
impl pedersen::Window for TestWindow {
    const WINDOW_SIZE: usize = 63;
    const NUM_WINDOWS: usize = NW;
}

pub const VK_FLAG: u64 = 3u64;
pub const AK_FLAG: u64 = 4u64;
pub const SK_FLAG: u64 = 5u64;

type Fr = <MNT4 as Pairing>::ScalarField;

pub struct PCDGm17Mnt4;
impl ECCyclePCDConfig<MNT4, MNT6> for PCDGm17Mnt4 {
    type CRH = CRH<EdwardsConfig, TestWindow>;
    type CRHGadget = CRHGadget<EdwardsConfig, FpVar<<MNT4 as Pairing>::ScalarField>>;

    type MainSNARK = GM17<MNT4>;
    type HelpSNARK = GM17<MNT6>;

    type MainSNARKGadget = GM17VerifierGadget<MNT4, MNT4PairingVar>;
    type HelpSNARKGadget = GM17VerifierGadget<MNT6, MNT6PairingVar>;
}

pub struct TestPredicate<F: PrimeField + Absorb> {
    pc: PoseidonConfig::<F>,
    new_j: Option<F>,
    vk: Option<F>,

    new_ak: Option<F>,
    old_j: Option<F>,
    old_ak: Option<F>,
    old_sk: Option<F>,
    new_sk: Option<F>,
}

impl<F: PrimeField + Absorb> TestPredicate<F> {
    fn new(pc: PoseidonConfig::<F>) -> Self {
        Self {
            pc: pc,
            new_j: None,
            vk: None,

            new_ak: None,
            old_j: None,
            old_ak: None,
            old_sk: None,
            new_sk: None,
        }
    }

    fn update(circ: TestPredicate<F>) -> Self {
        let old_j = circ.new_j;
        let old_ak = circ.new_ak;
        let old_sk = circ.new_sk;
        let new_sk = PCRH::<F>::evaluate(&circ.pc.clone(), vec![old_sk.unwrap(), F::from(SK_FLAG)]).unwrap();
        let new_j = circ.new_j.unwrap().add(F::from(1u64));
        let new_ak = PCRH::<F>::evaluate(&circ.pc.clone(), vec![new_sk, F::from(AK_FLAG)]).unwrap();
        Self {
            pc: circ.pc,
            new_j: Some(new_j),
            vk: circ.vk,
            new_ak: Some(new_ak),
            old_j: old_j,
            old_ak: old_ak,
            old_sk: old_sk,
            new_sk: Some(new_sk),
        }
    }
}

impl<F: PrimeField + Absorb> Clone for TestPredicate<F> {
    fn clone(&self) -> Self {
        Self {
            pc: self.pc.clone(),
            new_j: self.new_j.clone(),
            vk: self.vk.clone(),

            new_ak: self.new_ak.clone(),
            old_j: self.old_j.clone(),
            old_ak: self.old_ak.clone(),
            old_sk: self.old_sk.clone(),
            new_sk: self.new_sk.clone(),
        }
    }
}

impl<F: PrimeField + Absorb> PCDPredicate<F> for TestPredicate<F> {
    type Message = F;
    type MessageVar = FpVar<F>;

    const MSG_LEN: usize = 3;
    const PRIOR_PROOF_NUM: usize = 1;

    fn generate_constraints(
        &self,
        cs: ConstraintSystemRef<F>,
        msg: &[Self::MessageVar],
        prior_msgs: &[&[Self::MessageVar]],
        base_case: &Boolean<F>,
    ) -> Result<(), SynthesisError> {
        //////////prior_msgs equality check???????????
/*
        let new_j = self.new_j.unwrap_or_default();
        let new_j_var = FpVar::<F>::new_input(ark_relations::ns!(cs, "new j"), || Ok(new_j))?;
        let vk = self.vk.unwrap_or_default();
        let vk_var = FpVar::<F>::new_input(ark_relations::ns!(cs, "vk"), || Ok(vk))?;
        let new_ak = self.new_ak.unwrap_or_default();
        let new_ak_var = FpVar::<F>::new_input(ark_relations::ns!(cs, "new ak"), || Ok(new_ak))?;

        let old_j = self.old_j.unwrap_or_default();
        let old_j_var = FpVar::<F>::new_witness(ark_relations::ns!(cs, "old j"), || Ok(old_j))?;
        let old_ak = self.old_ak.unwrap_or_default();
        let old_ak_var = FpVar::<F>::new_witness(ark_relations::ns!(cs, "old ak"), || Ok(old_ak))?;
        let old_sk = self.old_sk.unwrap_or_default();
        let old_sk_var = FpVar::<F>::new_witness(ark_relations::ns!(cs, "old sk"), || Ok(old_sk))?;
        let new_sk = self.new_sk.unwrap_or_default();
        let new_sk_var = FpVar::<F>::new_witness(ark_relations::ns!(cs, "new sk"), || Ok(new_sk))?;
*/
        //&msg[0]
        //let new_j_value = self.new_j;
        //let new_j = cs.new_input_variable(|| new_j_value.ok_or(SynthesisError::AssignmentMissing))?;
        //&msg[1]
        //let vk_value = self.vk;
        //let vk = cs.new_input_variable(|| vk_value.ok_or(SynthesisError::AssignmentMissing))?;
        //&msg[2]
        //let new_ak_value = self.new_ak;
        //let new_ak = cs.new_input_variable(|| new_ak_value.ok_or(SynthesisError::AssignmentMissing))?;

        let old_j_value = self.old_j;
        let old_j = cs.new_witness_variable(|| old_j_value.ok_or(SynthesisError::AssignmentMissing))?;
        let old_ak_value = self.old_ak;
        let old_ak = cs.new_witness_variable(|| old_ak_value.ok_or(SynthesisError::AssignmentMissing))?;
        let old_sk_value = self.old_sk;
        let old_sk = cs.new_witness_variable(|| old_sk_value.ok_or(SynthesisError::AssignmentMissing))?;
        let new_sk_value = self.new_sk;
        let new_sk = cs.new_witness_variable(|| new_sk_value.ok_or(SynthesisError::AssignmentMissing))?;

        //let new_j_var = FpVar::Var(AllocatedFp::new(new_j_value, new_j, cs.clone()));
        //let vk_var = FpVar::Var(AllocatedFp::new(vk_value, vk, cs.clone()));
        //let new_ak_var = FpVar::Var(AllocatedFp::new(new_ak_value, new_ak, cs.clone()));
        let old_j_var = FpVar::Var(AllocatedFp::new(old_j_value, old_j, cs.clone()));
        let old_ak_var = FpVar::Var(AllocatedFp::new(old_ak_value, old_ak, cs.clone()));
        let new_sk_var = FpVar::Var(AllocatedFp::new(new_sk_value, new_sk, cs.clone()));
        let old_sk_var = FpVar::Var(AllocatedFp::new(old_sk_value, old_sk, cs.clone()));

        let one_var = FpVar::<F>::new_witness(ark_relations::ns!(cs, "ONE"), || Ok(F::from(1u64)))?;
        let vk_flag_var = FpVar::<F>::new_witness(ark_relations::ns!(cs, "VK_FLAG"), || Ok(F::from(VK_FLAG)))?;
        let ak_flag_var = FpVar::<F>::new_witness(ark_relations::ns!(cs, "AK_FLAG"), || Ok(F::from(AK_FLAG)))?;
        let sk_flag_var = FpVar::<F>::new_witness(ark_relations::ns!(cs, "SK_FLAG"), || Ok(F::from(SK_FLAG)))?;


        let pc = PCRHParametersVar::<F>::new_witness(cs.clone(), || Ok(self.pc.clone())).unwrap();

        let new_sk_to_vk_var = PCRHGadget::<F>::evaluate(&pc, &[new_sk_var.clone(), vk_flag_var])?;
        let old_sk_to_ak_var = PCRHGadget::<F>::evaluate(&pc, &[old_sk_var.clone(), ak_flag_var.clone()])?;
        let old_sk_to_sk_var = PCRHGadget::<F>::evaluate(&pc, &[old_sk_var, sk_flag_var])?;
        let new_sk_to_ak_var = PCRHGadget::<F>::evaluate(&pc, &[new_sk_var.clone(), ak_flag_var])?;
/*
        println!("new_sk_to_vk_var: {:?}", new_sk_to_vk_var.value());   //value()
        println!("old_sk_to_ak_var: {:?}", old_sk_to_ak_var.value());   //value()
        println!("old_sk_to_sk_var: {:?}", old_sk_to_sk_var.value());   //value()
        println!("new_sk_to_ak_var: {:?}", new_sk_to_ak_var.value());   //value()
*/
/*
        cs.enforce_constraint(
            lc!() + old_j + Variable::One,//(self.constants[1], Variable::One),
            lc!() + Variable::One,
            lc!() + new_j,
        )?;
*/
        let j_var = old_j_var.add(one_var);
        j_var.enforce_equal(&msg[0])?;

        new_sk_to_ak_var.enforce_equal(&msg[2])?;

        let sk_to_vk_check_pass = new_sk_to_vk_var.is_eq(&msg[1])?;

//FirstAid
        let same_vk_check_pass = msg[1].is_eq(&prior_msgs[0][1])?;
        let same_ak_check_pass = old_ak_var.is_eq(&prior_msgs[0][2])?;
//

        let sk_to_ak_check_pass = old_sk_to_ak_var.is_eq(&old_ak_var)?;
        let sk_to_sk_check_pass = old_sk_to_sk_var.is_eq(&new_sk_var)?;
        let true_only_if_base_case = base_case.and(&sk_to_vk_check_pass)?;
        let check_non_base_case = sk_to_ak_check_pass.and(&sk_to_sk_check_pass)?;
//FirstAid
        let check_non_base_case = check_non_base_case.and(&same_vk_check_pass)?;
        let check_non_base_case = check_non_base_case.and(&same_ak_check_pass)?;
//

        let should_be_true = true_only_if_base_case.or(&check_non_base_case)?;
        should_be_true.enforce_equal(&Boolean::constant(true))?;

        Ok(())
    }
}

type TestPCD = ECCyclePCD<EdwardsConfig, TestWindow, MNT4, MNT6, PCDGm17Mnt4>;





use ark_relations::r1cs::ConstraintSynthesizer;

struct SignDemo<F: PrimeField + Absorb> {
    pc2: PoseidonConfig::<F>,
    pc3: PoseidonConfig::<F>,
    j: Option<F>,
    vk: Option<F>,
    m: Option<F>,
    sk: Option<F>,
    ak: Option<F>,
    c_sig: Option<F>,
}
impl<F: PrimeField + Absorb> ConstraintSynthesizer<F> for SignDemo<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let j_value = self.j;
        let j = cs.new_witness_variable(|| j_value.ok_or(SynthesisError::AssignmentMissing))?;
        let vk_value = self.vk;
        let vk = cs.new_witness_variable(|| vk_value.ok_or(SynthesisError::AssignmentMissing))?;
        let m_value = self.m;
        let m = cs.new_witness_variable(|| m_value.ok_or(SynthesisError::AssignmentMissing))?;
        let sk_value = self.sk;
        let sk = cs.new_witness_variable(|| sk_value.ok_or(SynthesisError::AssignmentMissing))?;
//////////////// INPUT
        let ak_value = self.ak;
        let ak = cs.new_input_variable(|| ak_value.ok_or(SynthesisError::AssignmentMissing))?;
        let c_sig_value = self.c_sig;
        let c_sig = cs.new_input_variable(|| c_sig_value.ok_or(SynthesisError::AssignmentMissing))?;
//////////////// INPUT
        let j_var = FpVar::Var(AllocatedFp::new(j_value, j, cs.clone()));
        let vk_var = FpVar::Var(AllocatedFp::new(vk_value, vk, cs.clone()));
        let m_var = FpVar::Var(AllocatedFp::new(m_value, m, cs.clone()));
        let sk_var = FpVar::Var(AllocatedFp::new(sk_value, sk, cs.clone()));
        let ak_var = FpVar::Var(AllocatedFp::new(ak_value, ak, cs.clone()));
        let c_sig_var = FpVar::Var(AllocatedFp::new(c_sig_value, c_sig, cs.clone()));

        let ak_flag_var = FpVar::<F>::new_witness(ark_relations::ns!(cs, "AK_FLAG"), || Ok(F::from(AK_FLAG)))?;

        let pc2 = PCRHParametersVar::<F>::new_witness(cs.clone(), || Ok(self.pc2.clone())).unwrap();
        let pc3 = PCRHParametersVar::<F>::new_witness(cs.clone(), || Ok(self.pc3.clone())).unwrap();

        let sk_to_ak_var = PCRHGadget::<F>::evaluate(&pc2, &[sk_var, ak_flag_var])?;
        let sig_var = PCRHGadget::<F>::evaluate(&pc3, &[j_var, vk_var, m_var])?;

        ak_var.enforce_equal(&sk_to_ak_var)?;
        c_sig_var.enforce_equal(&sig_var)?;

        Ok(())
    }
}









fn main() {
    let mut rng = &mut ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
    let mut test_rng = test_rng();
    let mut mds = vec![vec![]; 3];
    for i in 0..3 {
        for _ in 0..3 {
            mds[i].push(Fr::rand(&mut test_rng));
        }
    }

    let mut ark = vec![vec![]; 8 + 24];
    for i in 0..8 + 24 {
        for _ in 0..3 {
            ark[i].push(Fr::rand(&mut test_rng));
        }
    }
    let pc = PoseidonConfig::<Fr>::new(8, 24, 31, mds, ark, 2, 1);
    //println!("pc : {:?}", pc);
    /*  full_rounds: usize,
        partial_rounds: usize,
        alpha: u64,
        ark: Vec<Vec<F>>,
        mds: Vec<Vec<F>>,
        rate: usize,
        capacity: usize,
    */
    //get_default_poseidon_parameters(2, false).unwrap();

    println!("SETUP");
    let start = Instant::now();
    let mut circ = TestPredicate::<Fr>::new(pc.clone());
    let (pk, vk) = TestPCD::circuit_specific_setup(&circ, &mut rng).unwrap();
    println!("setup time: {:?}", start.elapsed());
    println!("pksize: {:?}", pk.uncompressed_size());
    println!("vksize: {:?}", vk.uncompressed_size());



    let old_j = Fr::from(0u64);
    let old_ak = Fr::rand(&mut test_rng);//None;
    let old_sk = Fr::rand(&mut test_rng);//None;
    let new_sk = Fr::rand(&mut test_rng);

    let new_j = Fr::from(1u64);
    let vk_input = PCRH::<Fr>::evaluate(&pc, vec![new_sk.clone(), Fr::from(VK_FLAG)]).unwrap();
    let new_ak = PCRH::<Fr>::evaluate(&pc, vec![new_sk, Fr::from(AK_FLAG)]).unwrap();

    circ = TestPredicate {
        pc: pc.clone(),
        new_j: Some(new_j),
        vk: Some(vk_input),
        new_ak: Some(new_ak),
        old_j: Some(old_j),
        old_ak: Some(old_ak),
        old_sk: Some(old_sk),
        new_sk: Some(new_sk),
    };

    println!("PROVE");
    let start = Instant::now();
    let proof_1 = TestPCD::prove(&pk, &circ, &[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_ak.unwrap()], &[], &[], &mut rng).unwrap();
    println!("prove time: {:?}", start.elapsed());
    println!("[Signature 2] proof1size: {:?}", proof_1.uncompressed_size());
    println!("Verify");
    let start = Instant::now();
    assert!(TestPCD::verify::<TestPredicate<Fr>>(&vk, &[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_ak.unwrap()], &proof_1).unwrap());
    println!("veritfy time: {:?}", start.elapsed());
    println!("(Ignore This Since j,vk is public and ak is duplicate) [Signature 1] statementsize: {:?}", [circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_ak.unwrap()].uncompressed_size());

    circ = TestPredicate::<Fr>::update(circ);

    println!("PROVE");
    let start = Instant::now();
    let proof_2 = TestPCD::prove(&pk, &circ, &[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_ak.unwrap()], &[&[circ.old_j.unwrap(), circ.vk.unwrap(), circ.old_ak.unwrap()]], &vec![proof_1], &mut rng).unwrap();
    println!("prove time: {:?}", start.elapsed());
    println!("[Signature 2] proof2size: {:?}", proof_2.uncompressed_size());
    println!("Verify");
    let start = Instant::now();
    assert!(TestPCD::verify::<TestPredicate<Fr>>(&vk, &[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_ak.unwrap()], &proof_2).unwrap());
    println!("veritfy time: {:?}", start.elapsed());
    println!("(Ignore This Since j,vk is public and ak is duplicate) [Signature 1] statementsize: {:?}", [circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_ak.unwrap()].uncompressed_size());



    circ = TestPredicate::<Fr>::update(circ);

    println!("PROVE");
    let start = Instant::now();
    let proof_3 = TestPCD::prove(&pk, &circ, &[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_ak.unwrap()], &[&[circ.old_j.unwrap(), circ.vk.unwrap(), circ.old_ak.unwrap()]], &vec![proof_2], &mut rng).unwrap();
    println!("prove time: {:?}", start.elapsed());
    println!("[Signature 2] proof3size: {:?}", proof_3.uncompressed_size());
    println!("Verify");
    let start = Instant::now();
    assert!(TestPCD::verify::<TestPredicate<Fr>>(&vk, &[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_ak.unwrap()], &proof_3).unwrap());
    println!("veritfy time: {:?}", start.elapsed());
    println!("(Ignore This Since j,vk is public and ak is duplicate) [Signature 1] statementsize: {:?}", [circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_ak.unwrap()].uncompressed_size());



    circ = TestPredicate::<Fr>::update(circ);

    println!("PROVE");
    let start = Instant::now();
    let proof_4 = TestPCD::prove(&pk, &circ, &[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_ak.unwrap()], &[&[circ.old_j.unwrap(), circ.vk.unwrap(), circ.old_ak.unwrap()]], &vec![proof_3], &mut rng).unwrap();
    println!("prove time: {:?}", start.elapsed());
    println!("[Signature 2] proof4size: {:?}", proof_4.uncompressed_size());
    println!("Verify");
    let start = Instant::now();
    assert!(TestPCD::verify::<TestPredicate<Fr>>(&vk, &[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_ak.unwrap()], &proof_4).unwrap());
    println!("veritfy time: {:?}", start.elapsed());
    println!("(Ignore This Since j,vk is public and ak is duplicate) [Signature 1] statementsize: {:?}", [circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_ak.unwrap()].uncompressed_size());


    circ = TestPredicate::<Fr>::update(circ);

    println!("PROVE");
    let start = Instant::now();
    let proof_5 = TestPCD::prove(&pk, &circ, &[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_ak.unwrap()], &[&[circ.old_j.unwrap(), circ.vk.unwrap(), circ.old_ak.unwrap()]], &vec![proof_4], &mut rng).unwrap();
    println!("prove time: {:?}", start.elapsed());
    println!("[Signature 2] proof5size: {:?}", proof_5.uncompressed_size());
    println!("Verify");
    let start = Instant::now();
    assert!(TestPCD::verify::<TestPredicate<Fr>>(&vk, &[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_ak.unwrap()], &proof_5).unwrap());
    println!("veritfy time: {:?}", start.elapsed());
    println!("(Ignore This Since j,vk is public and ak is duplicate) [Signature 1] statementsize: {:?}", [circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_ak.unwrap()].uncompressed_size());
    //println!("test: {:?}", TestPredicate::<Fr>::PRIOR_PROOF_NUM);
/*
    println!("new_j : {:?}", circ.new_j);
    println!("vk : {:?}", circ.vk);
    println!("new_ak : {:?}", circ.new_ak);
    println!("old_j : {:?}", circ.old_j);
    println!("old_ak : {:?}", circ.old_ak);
    println!("old_sk : {:?}", circ.old_sk);
    println!("new_sk : {:?}", circ.new_sk);
*/

    use ark_crypto_primitives::snark::SNARK;
    use ark_crypto_primitives::snark::CircuitSpecificSetupSNARK;
    println!("START");


    let mut mds = vec![vec![]; 3];
    for i in 0..3 {
        for _ in 0..3 {
            mds[i].push(Fr::rand(&mut test_rng));
        }
    }

    let mut ark = vec![vec![]; 8 + 24];
    for i in 0..8 + 24 {
        for _ in 0..3 {
            ark[i].push(Fr::rand(&mut test_rng));
        }
    }
    let pc3 = PoseidonConfig::<Fr>::new(8, 24, 31, mds, ark, 2, 1);

    let start = Instant::now();
    // Create parameters for our circuit
    let (pk, vk) = {
        let sign_circ = SignDemo::<Fr> {
            pc2: pc.clone(),
            pc3: pc3.clone(),
            j: None,
            vk: None,
            ak: None,
            m: None,
            sk: None,
            c_sig: None,
        };
        GM17::<MNT4>::setup(sign_circ, &mut rng).unwrap()
    };
    // Prepare the verification key (for proof verification)
    let pvk = GM17::<MNT4>::process_vk(&vk).unwrap();
    println!("sign setup time: {:?}", start.elapsed());
    println!("pksize: {:?}", pk.uncompressed_size());
    //println!("vksize: {:?}", vk.uncompressed_size());
    println!("pvksize: {:?}", pvk.uncompressed_size());

    let j = circ.new_j;
    let vk = circ.vk;
    let m = Fr::rand(&mut test_rng);
    let sk = circ.new_sk;
    let ak = PCRH::<Fr>::evaluate(&pc, vec![sk.unwrap(), Fr::from(AK_FLAG)]).unwrap();
    let c_sig = PCRH::<Fr>::evaluate(&pc3, vec![j.unwrap(), vk.unwrap(), m]).unwrap();

/*
    println!("j : {:?}", j);
    println!("vk : {:?}", circ.vk);
    println!("ak : {:?}", ak);
    println!("m : {:?}", m);
    println!("sk : {:?}", sk);
    println!("c_sk_to_ak : {:?}", c_sk_to_ak);
    println!("c_sig : {:?}", c_sig);
*/

    let start = Instant::now();
    let sign_circ = SignDemo {
        pc2: pc,
        pc3: pc3,
        j: j,
        vk: vk,
        m: Some(m),
        sk: sk,
        ak: Some(ak),
        c_sig: Some(c_sig),
    };
    let proof = GM17::<MNT4>::prove(&pk, sign_circ, &mut rng).unwrap();
    println!("sign proving time: {:?}", start.elapsed());
    println!("[Signature 4] proofsize: {:?}", proof.uncompressed_size());

    let start = Instant::now();
    assert!( GM17::<MNT4>::verify_with_processed_vk(&pvk, &[ak, c_sig], &proof).unwrap() );        
    println!("sign verifying time: {:?}", start.elapsed());
    println!("[Signature 3] statementsize: {:?}", [ak, c_sig].uncompressed_size());


    println!("[Secret key] size: {:?}", sk.uncompressed_size());
    println!("[Verification key] size: {:?}", vk.uncompressed_size());    

/* CIRCUIT
        println!("c_sig_var: {:?}", c_sig_var.value());
        println!("sig_var: {:?}", sig_var.value());
        println!("sk_to_ak_var: {:?}", sk_to_ak_var.value());
        println!("ak_var: {:?}", ak_var.value());
*/
}
