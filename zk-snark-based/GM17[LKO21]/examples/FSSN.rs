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
use ark_pcd::ec_cycle_pcd::{ECCyclePCD, Terminal_ECCyclePCD, ECCyclePCDConfig};

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
use ark_pcd::{PCDPredicate, PCD, Terminal_PCDPredicate, Terminal_PCD};
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

    old_j: Option<F>,
    old_sk: Option<F>,
    new_sk: Option<F>,
}

impl<F: PrimeField + Absorb> TestPredicate<F> {
    fn new(pc: PoseidonConfig::<F>) -> Self {
        Self {
            pc: pc,
            new_j: None,
            vk: None,

            old_j: None,
            old_sk: None,
            new_sk: None,
        }
    }

    fn update(circ: TestPredicate<F>) -> Self {
        let old_j = circ.new_j;
        let old_sk = circ.new_sk;
        let new_sk = PCRH::<F>::evaluate(&circ.pc.clone(), vec![old_sk.unwrap(), F::from(SK_FLAG)]).unwrap();
        let new_j = circ.new_j.unwrap().add(F::from(1u64));
        Self {
            pc: circ.pc,
            new_j: Some(new_j),
            vk: circ.vk,
            old_j: old_j,
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

            old_j: self.old_j.clone(),
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
        let old_j_value = self.old_j;
        let old_j = cs.new_witness_variable(|| old_j_value.ok_or(SynthesisError::AssignmentMissing))?;
        let old_sk_value = self.old_sk;
        let old_sk = cs.new_witness_variable(|| old_sk_value.ok_or(SynthesisError::AssignmentMissing))?;

        let old_j_var = FpVar::Var(AllocatedFp::new(old_j_value, old_j, cs.clone()));
        let old_sk_var = FpVar::Var(AllocatedFp::new(old_sk_value, old_sk, cs.clone()));



        let one_var = FpVar::<F>::new_witness(ark_relations::ns!(cs, "ONE"), || Ok(F::from(1u64)))?;
        let vk_flag_var = FpVar::<F>::new_witness(ark_relations::ns!(cs, "VK_FLAG"), || Ok(F::from(VK_FLAG)))?;
        let sk_flag_var = FpVar::<F>::new_witness(ark_relations::ns!(cs, "SK_FLAG"), || Ok(F::from(SK_FLAG)))?;



        let pc = PCRHParametersVar::<F>::new_witness(cs.clone(), || Ok(self.pc.clone())).unwrap();

        let new_sk_to_vk_var = PCRHGadget::<F>::evaluate(&pc, &[msg[2].clone(), vk_flag_var])?;
        let old_sk_to_sk_var = PCRHGadget::<F>::evaluate(&pc, &[old_sk_var, sk_flag_var])?;

        let j_var = old_j_var.add(one_var);
        j_var.enforce_equal(&msg[0])?;

        let sk_to_vk_check_pass = new_sk_to_vk_var.is_eq(&msg[1])?;
        
//FirstAid
        let same_vk_check_pass = msg[1].is_eq(&prior_msgs[0][1])?;
//

        let sk_to_sk_check_pass = old_sk_to_sk_var.is_eq(&msg[2])?;
        let true_only_if_base_case = base_case.and(&sk_to_vk_check_pass)?;
        let check_non_base_case = sk_to_sk_check_pass.and(&same_vk_check_pass)?;

        let should_be_true = true_only_if_base_case.or(&check_non_base_case)?;
        should_be_true.enforce_equal(&Boolean::constant(true))?;

        Ok(())
    }
}

pub struct SignDemo<F: PrimeField + Absorb> {
    pc3: PoseidonConfig::<F>,
    j: Option<F>,       //msg[0]
    vk: Option<F>,      //msg[1]
    m: Option<F>,       //msg[2]
    c_sig: Option<F>,
}
impl<F: PrimeField + Absorb> SignDemo<F> {
    fn new(pc3: PoseidonConfig::<F>) -> Self {
        Self {
            pc3: pc3,
            j: None,
            vk: None,
            m: None,
            c_sig: None,
        }
    }
}
impl<F: PrimeField + Absorb> Clone for SignDemo<F> {
    fn clone(&self) -> Self {
        Self {
            pc3: self.pc3.clone(),
            j: self.j.clone(),
            vk: self.vk.clone(),
            m: self.m.clone(),
            c_sig: self.c_sig.clone(),
        }
    }
}
impl<F: PrimeField + Absorb> Terminal_PCDPredicate<F> for SignDemo<F> {
    type Message = F;
    type MessageVar = FpVar<F>;

    const PRIOR_MSG_LEN: usize = 3;
    const MSG_LEN: usize = 3;
    const PRIOR_PROOF_NUM: usize = 1;

    fn generate_constraints(
        &self,
        cs: ConstraintSystemRef<F>,
        msg: &[Self::MessageVar],
        prior_msgs: &[&[Self::MessageVar]],
    ) -> Result<(), SynthesisError> {

        //////////prior_msgs equality check???????????
        //let j_value = self.j;
        //let j = cs.new_witness_variable(|| j_value.ok_or(SynthesisError::AssignmentMissing))?;
        //let vk_value = self.vk;
        //let vk = cs.new_witness_variable(|| vk_value.ok_or(SynthesisError::AssignmentMissing))?;
        let m_value = self.m;
        let m = cs.new_witness_variable(|| m_value.ok_or(SynthesisError::AssignmentMissing))?;
        //let c_sig_value = self.c_sig;
        //let c_sig = cs.new_input_variable(|| c_sig_value.ok_or(SynthesisError::AssignmentMissing))?;

        //let j_var = FpVar::Var(AllocatedFp::new(j_value, j, cs.clone()));
        //let vk_var = FpVar::Var(AllocatedFp::new(vk_value, vk, cs.clone()));
        let m_var = FpVar::Var(AllocatedFp::new(m_value, m, cs.clone()));
        //let c_sig_var = FpVar::Var(AllocatedFp::new(c_sig_value, c_sig, cs.clone()));


        let pc3 = PCRHParametersVar::<F>::new_witness(cs.clone(), || Ok(self.pc3.clone())).unwrap();

        let sig_var = PCRHGadget::<F>::evaluate(&pc3, &[msg[0].clone(), msg[1].clone(), m_var])?;

        sig_var.enforce_equal(&msg[2])?;

        let same_j_check_pass = msg[0].is_eq(&prior_msgs[0][0])?;
        let same_vk_check_pass = msg[1].is_eq(&prior_msgs[0][1])?;

        let check = same_j_check_pass.and(&same_vk_check_pass)?;
        check.enforce_equal(&Boolean::constant(true))?;

        Ok(())
    }
}

type TestPCD = ECCyclePCD<EdwardsConfig, TestWindow, MNT4, MNT6, PCDGm17Mnt4>;
type Terminal_TestPCD = Terminal_ECCyclePCD<EdwardsConfig, TestWindow, MNT4, MNT6, PCDGm17Mnt4>;


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

    println!("SETUP");
    let start = Instant::now();
    let mut circ = TestPredicate::<Fr>::new(pc.clone());
    let (pk, vk) = TestPCD::circuit_specific_setup(&circ, &mut rng).unwrap();
    println!("setup time: {:?}", start.elapsed());
    println!("pksize: {:?}", pk.uncompressed_size());
    println!("\tpk_crh_pp_size: {:?}", pk.crh_pp.uncompressed_size());
    println!("\tpk_main_pk_size: {:?}", pk.main_pk.uncompressed_size());
    println!("\tpk_help_pk_size: {:?}", pk.help_pk.uncompressed_size());
    println!("\tpk_help_vk_size: {:?}", pk.help_vk.uncompressed_size());
    println!("\tpk_main_pvk_size: {:?}", pk.main_pvk.uncompressed_size());
    println!("vksize: {:?}", vk.uncompressed_size());



    let old_j = Fr::from(0u64);
    let old_sk = Fr::rand(&mut test_rng);//None;
    let new_sk = Fr::rand(&mut test_rng);

    let new_j = Fr::from(1u64);
    let vk_input = PCRH::<Fr>::evaluate(&pc, vec![new_sk.clone(), Fr::from(VK_FLAG)]).unwrap();

    circ = TestPredicate {
        pc: pc.clone(),
        new_j: Some(new_j),
        vk: Some(vk_input),
        old_j: Some(old_j),
        old_sk: Some(old_sk),
        new_sk: Some(new_sk),
    };

    println!("PROVE");
    let start = Instant::now();
    let proof_1 = TestPCD::prove(&pk, &circ, &[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_sk.unwrap()], &[], &[], &mut rng).unwrap();
    println!("prove time: {:?}", start.elapsed());
    println!("proof1size: {:?}", proof_1.uncompressed_size());
    println!("Verify");
    let start = Instant::now();
    assert!(TestPCD::verify::<TestPredicate<Fr>>(&vk, &[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_sk.unwrap()], &proof_1).unwrap());
    println!("veritfy time: {:?}", start.elapsed());


    circ = TestPredicate::<Fr>::update(circ);

    println!("PROVE");
    let start = Instant::now();
    let proof_2 = TestPCD::prove(&pk, &circ, &[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_sk.unwrap()], &[&[circ.old_j.unwrap(), circ.vk.unwrap(), circ.old_sk.unwrap()]], &vec![proof_1], &mut rng).unwrap();
    println!("prove time: {:?}", start.elapsed());
    println!("proof2size: {:?}", proof_2.uncompressed_size());
    println!("Verify");
    let start = Instant::now();
    assert!(TestPCD::verify::<TestPredicate<Fr>>(&vk, &[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_sk.unwrap()], &proof_2).unwrap());
    println!("veritfy time: {:?}", start.elapsed());



    circ = TestPredicate::<Fr>::update(circ);

    println!("PROVE");
    let start = Instant::now();
    let proof_3 = TestPCD::prove(&pk, &circ, &[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_sk.unwrap()], &[&[circ.old_j.unwrap(), circ.vk.unwrap(), circ.old_sk.unwrap()]], &vec![proof_2], &mut rng).unwrap();
    println!("prove time: {:?}", start.elapsed());
    println!("proof3size: {:?}", proof_3.uncompressed_size());
    println!("Verify");
    let start = Instant::now();
    assert!(TestPCD::verify::<TestPredicate<Fr>>(&vk, &[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_sk.unwrap()], &proof_3).unwrap());
    println!("veritfy time: {:?}", start.elapsed());




    circ = TestPredicate::<Fr>::update(circ);

    println!("PROVE");
    let start = Instant::now();
    let proof_4 = TestPCD::prove(&pk, &circ, &[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_sk.unwrap()], &[&[circ.old_j.unwrap(), circ.vk.unwrap(), circ.old_sk.unwrap()]], &vec![proof_3], &mut rng).unwrap();
    println!("prove time: {:?}", start.elapsed());
    println!("proof4size: {:?}", proof_4.uncompressed_size());
    println!("Verify");
    let start = Instant::now();
    assert!(TestPCD::verify::<TestPredicate<Fr>>(&vk, &[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_sk.unwrap()], &proof_4).unwrap());
    println!("veritfy time: {:?}", start.elapsed());



    circ = TestPredicate::<Fr>::update(circ);

    println!("PROVE");
    let start = Instant::now();
    let proof_5 = TestPCD::prove(&pk, &circ, &[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_sk.unwrap()], &[&[circ.old_j.unwrap(), circ.vk.unwrap(), circ.old_sk.unwrap()]], &vec![proof_4], &mut rng).unwrap();
    println!("prove time: {:?}", start.elapsed());
    println!("proof5size: {:?}", proof_5.uncompressed_size());
    println!("Verify");
    let start = Instant::now();
    assert!(TestPCD::verify::<TestPredicate<Fr>>(&vk, &[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_sk.unwrap()], &proof_5).unwrap());
    println!("veritfy time: {:?}", start.elapsed());



/*
    println!("new_j : {:?}", circ.new_j);
    println!("vk : {:?}", circ.vk);
    println!("old_j : {:?}", circ.old_j);
    println!("old_sk : {:?}", circ.old_sk);
    println!("new_sk : {:?}", circ.new_sk);
*/





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


    let mut sign_circ = SignDemo::<Fr>::new(pc3.clone());

    let m = Fr::rand(&mut test_rng);
    let c_sig = PCRH::<Fr>::evaluate(&pc3, vec![circ.new_j.unwrap(), circ.vk.unwrap(), m]).unwrap();

    sign_circ = SignDemo {
        pc3: pc3.clone(),
        j: circ.new_j,
        vk: circ.vk,
        m: Some(m),
        c_sig: Some(c_sig),
    };

    println!("SETUP");
    let start = Instant::now();
    let (pk, vk) = Terminal_TestPCD::circuit_specific_setup(&sign_circ, pk.crh_pp.clone(), pk.help_vk.clone(), &[sign_circ.j.unwrap(), sign_circ.vk.unwrap(), sign_circ.c_sig.unwrap()], &[&[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_sk.unwrap()]], &vec![proof_5.clone()], &mut rng).unwrap();
    println!("setup time: {:?}", start.elapsed());
    println!("pksize: {:?}", pk.uncompressed_size());
    println!("\tpk_crh_pp_size: {:?}", pk.crh_pp.uncompressed_size());
    println!("\tpk_main_pk_size: {:?}", pk.main_pk.uncompressed_size());
    println!("\tpk_help_vk_size: {:?}", pk.help_vk.uncompressed_size());
    println!("vksize: {:?}", vk.uncompressed_size());
    

    println!("[Secret key 1] size: {:?}", proof_5.uncompressed_size());

    println!("PROVE");
    let start = Instant::now();
    let proof_s = Terminal_TestPCD::prove(&pk, &sign_circ, &[sign_circ.j.unwrap(), sign_circ.vk.unwrap(), sign_circ.c_sig.unwrap()], &[&[circ.new_j.unwrap(), circ.vk.unwrap(), circ.new_sk.unwrap()]], &vec![proof_5], &mut rng).unwrap();
    //circ.new_sk is used here


    println!("prove time: {:?}", start.elapsed());
    println!("[Signature 1] proof1size: {:?}", proof_s.uncompressed_size());
    println!("Verify");
    let start = Instant::now();
    assert!(Terminal_TestPCD::verify::<SignDemo<Fr>>(&vk, &[sign_circ.j.unwrap(), sign_circ.vk.unwrap(), sign_circ.c_sig.unwrap()], &proof_s).unwrap());
    println!("veritfy time: {:?}", start.elapsed());

    println!("[Signature 2] csig_of_statementsize: {:?}", sign_circ.c_sig.uncompressed_size());
    println!("[Secret key 2] size: {:?}", circ.new_sk.uncompressed_size());

    println!("[Verification key] size: {:?}", circ.vk.uncompressed_size());
}
