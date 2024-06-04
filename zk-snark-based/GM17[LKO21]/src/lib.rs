#![cfg_attr(not(feature = "std"), no_std)]
#![deny(unused_imports)]
#![allow(clippy::op_ref, clippy::type_complexity)]

use ark_ff::Field;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::ToBytesGadget;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_std::rand::{CryptoRng, RngCore};
use ark_std::boxed::Box;

pub type Error = Box<dyn ark_std::error::Error + 'static>;

pub trait PCDPredicate<F: Field>: Clone {
    type Message: Sized + Clone + Default;
    type MessageVar: ToBytesGadget<F> + AllocVar<Self::Message, F>;

    const MSG_LEN: usize;
    const PRIOR_PROOF_NUM: usize;

    fn generate_constraints(
        &self,
        cs: ConstraintSystemRef<F>,
        msg: &[Self::MessageVar],
        prior_msgs: &[&[Self::MessageVar]],
        base_case: &Boolean<F>,
    ) -> Result<(), SynthesisError>;
}

pub trait PCD<F: Field> {
    type ProvingKey: Clone;
    type VerifyingKey: Clone;
    type Proof: Clone;

    fn circuit_specific_setup<P: PCDPredicate<F>, R: RngCore + CryptoRng>(
        predicate: &P,
        rng: &mut R,
    ) -> Result<(<Self as PCD<F>>::ProvingKey, <Self as PCD<F>>::VerifyingKey), Error>;

    fn prove<P: PCDPredicate<F>, R: RngCore + CryptoRng>(
        predicate_pk: &Self::ProvingKey,
        predicate: &P,
        msg: &[P::Message],
        prior_msgs: &[&[P::Message]],
        prior_proofs: &[Self::Proof],
        rng: &mut R,
    ) -> Result<Self::Proof, Error>;

    fn verify<P: PCDPredicate<F>>(
        predicate_vk: &Self::VerifyingKey,
        msg: &[P::Message],
        proof: &Self::Proof,
    ) -> Result<bool, Error>;
}







pub trait Terminal_PCDPredicate<F: Field>: Clone {
    type Message: Sized + Clone + Default;
    type MessageVar: ToBytesGadget<F> + AllocVar<Self::Message, F>;

    const PRIOR_MSG_LEN: usize;
    const MSG_LEN: usize;
    const PRIOR_PROOF_NUM: usize;

    fn generate_constraints(
        &self,
        cs: ConstraintSystemRef<F>,
        msg: &[Self::MessageVar],
        prior_msgs: &[&[Self::MessageVar]],
    ) -> Result<(), SynthesisError>;
}

use ark_ec::{
    twisted_edwards::TECurveConfig,
    pairing::Pairing,
    //CurveGroup
};

use ark_crypto_primitives::{
    crh::{CRHScheme, },
    crh::bowe_hopwood::CRH,
    crh::pedersen,
    snark::SNARK,
};
use crate::ec_cycle_pcd::ECCyclePCDConfig;



pub trait Terminal_PCD<F: Field, CC: TECurveConfig, WINDOW: pedersen::Window, MainEngine: Pairing, HelpEngine: Pairing, IC: ECCyclePCDConfig<MainEngine, HelpEngine>> {
    type ProvingKey: Clone;
    type VerifyingKey: Clone;
    type MainProof: Clone;
    type HelpProof: Clone;

    fn circuit_specific_setup<P: Terminal_PCDPredicate<F>, R: RngCore + CryptoRng>(
        predicate: &P,
        crh_pp: <CRH<CC, WINDOW> as CRHScheme>::Parameters,
        help_vk: <IC::HelpSNARK as SNARK<HelpEngine::ScalarField>>::VerifyingKey,//SNARK<HelpEngine::ScalarField>::VerifyingKey,
        msg: &[P::Message],
        prior_msgs: &[&[P::Message]],
        prior_proofs: &[<IC::HelpSNARK as SNARK<HelpEngine::ScalarField>>::Proof],
        rng: &mut R,
    ) -> Result<(<Self as Terminal_PCD<F, CC, WINDOW, MainEngine, HelpEngine, IC>>::ProvingKey, <Self as Terminal_PCD<F, CC, WINDOW, MainEngine, HelpEngine, IC>>::VerifyingKey), Error>;

    fn prove<P: Terminal_PCDPredicate<F>, R: RngCore + CryptoRng>(
        predicate_pk: &Self::ProvingKey,
        predicate: &P,
        msg: &[P::Message],
        prior_msgs: &[&[P::Message]],
        prior_proofs: &[Self::HelpProof],
        rng: &mut R,
    ) -> Result<Self::MainProof, Error>;

    fn verify<P: Terminal_PCDPredicate<F>>(
        predicate_vk: &Self::VerifyingKey,
        msg: &[F],
        //msg: &[P::Message],       ////GIVE UP, I CANNOT FIX
        proof: &Self::MainProof,
    ) -> Result<bool, Error>;
}

pub mod ec_cycle_pcd;
