//cargo run --release --example FSSN
//! Forward Secure Signature with Nova (Update and Sign StepCircuit)
use bellpepper_core::{boolean::AllocatedBit, num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::PrimeField;
use ff::Field;
use flate2::{write::ZlibEncoder, Compression};
use nova_snark::{
  traits::{
    circuit::{StepCircuit, TrivialCircuit},
    snark::default_ck_hint,
    Engine, //Group,
  },
  CompressedSNARK, PublicParams, RecursiveSNARK,
  gadgets::utils::alloc_num_equals,
  spartan::direct::DirectSNARK,
};

use neptune::{
  circuit::poseidon_hash,
  poseidon::{Poseidon, PoseidonConstants},
  Strength,
};

use nova_snark::provider::{PallasEngine, VestaEngine};
type E1 = PallasEngine;
type E2 = VestaEngine;
type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<E1>;
/*
use nova_snark::provider::{mlkzg::Bn256EngineKZG, GrumpkinEngine};
type E1 = Bn256EngineKZG;
type E2 = GrumpkinEngine;
type EE1 = nova_snark::provider::mlkzg::EvaluationEngine<E1>;
*/
type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<E2>;
type S1 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E1, EE1>; // non-preprocessing SNARK
type S2 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E2, EE2>; // non-preprocessing SNARK

//choose one for DirectSnark////////////////////////////////////////////////////////////////////////
type S = S1;
//type S = nova_snark::spartan::ppsnark::RelaxedR1CSSNARK<E1, EE1>; //preprocessing SNARK
/////////////////////////////////////////////////////////////////////////////////////////////


use generic_array::typenum::U2;
use generic_array::typenum::U3;

use std::time::Instant;

pub const VK_FLAG: u64 = 3u64;
pub const AK_FLAG: u64 = 4u64;
pub const SK_FLAG: u64 = 5u64;

#[derive(Clone, Debug)]
struct FSSNCircuitUpdate<F:PrimeField> {
  pc: PoseidonConstants<F, U2>,
  old_sk: F,    //G1::Scalar
  new_sk: F,
}

impl<F: PrimeField> FSSNCircuitUpdate<F> {
  pub fn update_key(&self) -> Self {
    //let mut hasher = G2::RO::new(self.pp_ro_consts.clone(), 1);        //<E2 as Engine>
    //hasher.absorb(self.new_sk.clone());
    //hasher.squeeze(NUM_HASH_BITS)

    Self {
      pc: self.pc.clone(),
      old_sk: self.new_sk.clone(),
      new_sk: Poseidon::<F, U2>::new_with_preimage(&[self.new_sk, F::from(SK_FLAG)], &self.pc).hash()
    }
  }
}



impl<F: PrimeField> StepCircuit<F> for FSSNCircuitUpdate<F> {
  fn arity(&self) -> usize {
    2
  }

  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    z: &[AllocatedNum<F>],
    _is_base_case: Option<&AllocatedBit>,
  ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
    let vk = z[0].clone();
    let ak = z[1].clone();

    // we allocate a variable and set it to the provided non-deterministic advice.
    let old_sk = AllocatedNum::alloc(cs.namespace(|| "old sk"), || Ok(self.old_sk))?;
    let new_sk = AllocatedNum::alloc(cs.namespace(|| "new sk"), || Ok(self.new_sk))?;
    let vk_flag = AllocatedNum::alloc(cs.namespace(|| "VK_FLAG"), || Ok(F::from(VK_FLAG)))?;
    let ak_flag = AllocatedNum::alloc(cs.namespace(|| "AK_FLAG"), || Ok(F::from(AK_FLAG)))?;
    let sk_flag = AllocatedNum::alloc(cs.namespace(|| "SK_FLAG"), || Ok(F::from(SK_FLAG)))?;
//////////////////////////////////////////////////is FLAG should be a witness?

    let sk_to_vk = poseidon_hash(cs.namespace(|| "sk_to_vk hash"), vec![new_sk.clone(), vk_flag], &self.pc)?;
    //cs.enforce(|| "check sk_to_vk", |lc| lc + vk.clone().get_variable(), |lc| lc + CS::one(), |lc| lc + sk_to_vk.get_variable());
    let sk_to_ak = poseidon_hash(cs.namespace(|| "sk_to_ak hash"), vec![old_sk.clone(), ak_flag.clone()], &self.pc)?;
    //cs.enforce(|| "check sk_to_ak", |lc| lc + ak.get_variable(), |lc| lc + CS::one(), |lc| lc + sk_to_ak.get_variable());
    let sk_to_sk = poseidon_hash(cs.namespace(|| "sk_to_sk hash"), vec![old_sk.clone(), sk_flag], &self.pc)?;
    //cs.enforce(|| "check sk_to_sk", |lc| lc + new_sk.get_variable(), |lc| lc + CS::one(), |lc| lc + sk_to_sk.get_variable());
    let new_ak = poseidon_hash(cs.namespace(|| "new_ak hash"), vec![new_sk.clone(), ak_flag], &self.pc)?;


    let sk_to_vk_check_pass = alloc_num_equals(
      cs.namespace(|| "check sk_to_vk"),
      &vk,
      &sk_to_vk,
    )?;

    let sk_to_ak_check_pass = alloc_num_equals(
      cs.namespace(|| "check sk_to_ak"),
      &ak,
      &sk_to_ak,
    )?;

    let sk_to_sk_check_pass = alloc_num_equals(
      cs.namespace(|| "check sk_to_sk"),
      &new_sk,
      &sk_to_sk,
    )?;

    /////////////////////////////////////////////////
    //should_be_false = nor(
    //  and(sk_to_ak_check_pass, sk_to_sk_check_pass)
    //  and(_is_base_case, sk_to_vk_check_pass)
    //)
    /////////////////////////////////////////////////

    let true_only_if_base_case = AllocatedBit::and ( 
      cs.namespace(|| "true_only_if_base_case"),
      _is_base_case.unwrap(),
      &sk_to_vk_check_pass,
    )?;

    let check_non_base_case = AllocatedBit::and (
      cs.namespace(|| "check_non_base_case"),
      &sk_to_ak_check_pass,
      &sk_to_sk_check_pass,
    )?;

    let should_be_false = AllocatedBit::nor (
      cs.namespace(|| "true_only_if_base_case nor check_non_base_case"),
      &true_only_if_base_case,
      &check_non_base_case,
    )?;
    cs.enforce(
      || "should_be_false",
      |lc| lc + should_be_false.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc,
    );


    Ok(vec![vk, new_ak])    //it enforce new vk = old vk
  }

}



#[derive(Clone, Debug, Default)]
struct FSSNCircuitSign<F: PrimeField> {
  pc2: PoseidonConstants<F, U2>,
  pc3: PoseidonConstants<F, U3>,
  sk: F,
  //period: F,
  //vk: F,
  message: F,
}
impl<F: PrimeField> StepCircuit<F> for FSSNCircuitSign<F> {
  fn arity(&self) -> usize {
    4
  }

  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    z: &[AllocatedNum<F>],
    _is_base_case: Option<&AllocatedBit>,
  ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
    let vk = z[0].clone();
    let period = z[1].clone();
    let c_sk_to_ak = z[2].clone();
    let c_sig = z[3].clone();

    //let zero_padding_for_even = AllocatedNum::alloc_input(cs.namespace(|| "zero_padding_for_even"), || Ok(F::from(0u64)))?;
    let sk = AllocatedNum::alloc(cs.namespace(|| "sk"), || Ok(self.sk))?;
    let ak_flag = AllocatedNum::alloc(cs.namespace(|| "AK_FLAG"), || Ok(F::from(AK_FLAG)))?;
    let sk_to_ak = poseidon_hash(cs.namespace(|| "sk_to_ak"), vec![sk, ak_flag], &self.pc2)?;

    let message = AllocatedNum::alloc(cs.namespace(|| "message"), || Ok(self.message))?;
    let sig = poseidon_hash(cs.namespace(|| "sign function"), vec![period.clone(), vk.clone(), message.clone()], &self.pc3)?;

    cs.enforce(
      || "c_sk_to_ak == sk_to_ak",
      |lc| lc + c_sk_to_ak.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + sk_to_ak.get_variable(),
    );

    cs.enforce(
      || "c_sig == sig",
      |lc| lc + c_sig.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + sig.get_variable(),
    );

    Ok(vec![vk, period, sk_to_ak, sig])
  }
}

impl<F: PrimeField> FSSNCircuitSign<F> {
  fn output(&self, z: &[F]) -> Vec<F> {
    vec![
      z[0],
      z[1],
      Poseidon::<F, U2>::new_with_preimage(&[self.sk, F::from(AK_FLAG)], &self.pc2).hash(),
      Poseidon::<F, U3>::new_with_preimage(&[z[1], z[0], self.message], &self.pc3).hash()
    ]
  }
}




fn main() {
  println!("Nova-based FSSN");
  println!("=========================================================");

  let num_steps = 10;
  let rng = &mut rand::rngs::OsRng;
  
  let pc = PoseidonConstants::<<E1 as Engine>::Scalar, U2>::new_with_strength(Strength::Standard);
  let pc3 = PoseidonConstants::<<E1 as Engine>::Scalar, U3>::new_with_strength(Strength::Standard);

  //is mut safe?
  let mut circuit_primary = FSSNCircuitUpdate {
    pc: pc.clone(),
    old_sk: <E1 as Engine>::Scalar::zero(),        //<<E2 as Engine>::Base as Field>::zero(),
    new_sk: <E1 as Engine>::Scalar::random(rng),   //[base_case] It determines vk!
  };

  let circuit_secondary = TrivialCircuit::default();

  type C1 = FSSNCircuitUpdate<<E1 as Engine>::Scalar>;
  type C2 = TrivialCircuit<<E2 as Engine>::Scalar>;

  println!("old_sk: {:#?}", circuit_primary.old_sk);
  println!("new_sk: {:?}", circuit_primary.new_sk);
  println!("gen_vk: {:?}", Poseidon::<<E1 as Engine>::Scalar, U2>::new_with_preimage(&[circuit_primary.new_sk, <E1 as Engine>::Scalar::from(VK_FLAG)], &circuit_primary.pc).hash());
  println!("new_ak: {:?}", Poseidon::<<E1 as Engine>::Scalar, U2>::new_with_preimage(&[circuit_primary.new_sk, <E1 as Engine>::Scalar::from(AK_FLAG)], &circuit_primary.pc).hash());

  // produce public parameters
  let start = Instant::now();
//// //preprocessing SNARK
/*
  type EE<E> = nova_snark::provider::ipa_pc::EvaluationEngine<E>;
  type SPrime<E, EE> = nova_snark::spartan::ppsnark::RelaxedR1CSSNARK<E, EE>;
  //this tests public parameters with a size specifically intended for a spark-compressed SNARK
  let ck_hint1 = &*SPrime::<E1, EE<E1>>::ck_floor();
  let ck_hint2 = &*SPrime::<E2, EE<E2>>::ck_floor();
*/
  let ck_hint1 = &*default_ck_hint();
  let ck_hint2 = &*default_ck_hint();
    
  println!("Producing public parameters...");
  let pp = PublicParams::<
    E1,
    E2,
    C1,
    C2,
  >::setup(&circuit_primary, &circuit_secondary, ck_hint1, ck_hint2);
  println!("PublicParams::setup, took {:?} ", start.elapsed());

  //serialized_data
  println!("Serialized size: {} bytes", bincode::serialize(&pp).unwrap().len());        //pp: PublicParams<E1, E2, C1, C2>
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  println!("Number of constraints per step (primary circuit): {}", pp.num_constraints().0);
  println!("Number of constraints per step (secondary circuit): {}", pp.num_constraints().1);
  println!("Number of variables per step (primary circuit): {}", pp.num_variables().0);
  println!("Number of variables per step (secondary circuit): {}",pp.num_variables().1);

  let z0_primary = vec![
    Poseidon::<<E1 as Engine>::Scalar, U2>::new_with_preimage(&[circuit_primary.new_sk, <E1 as Engine>::Scalar::from(VK_FLAG)], &circuit_primary.pc).hash(),
    <E1 as Engine>::Scalar::zero()   //is this should be hash of "new_sk"???? (I think it is not necessary)
  ];
  let z0_secondary = vec![<E2 as Engine>::Scalar::zero()];

  // produce a recursive SNARK
  println!("Generating a RecursiveSNARK...");

  let mut recursive_snark: RecursiveSNARK<E1, E2, C1, C2> = RecursiveSNARK::new(
    &pp,
    &circuit_primary,
    &circuit_secondary,
    &z0_primary,
    &z0_secondary,
  )
  .unwrap();

  println!("[Secret key 1] Serialized size: {} bytes", bincode::serialize(&circuit_primary.old_sk).unwrap().len());
  println!("[Secret key 2] Serialized size: {} bytes", bincode::serialize(&recursive_snark).unwrap().len());

  for i in 0..num_steps {
    if i != 0 { circuit_primary = circuit_primary.update_key(); }
    let start = Instant::now();
    let res = recursive_snark.prove_step(
      &pp,
      &circuit_primary,
      &circuit_secondary,
    );
    assert!(res.is_ok());
    println!(
      "RecursiveSNARK::prove_step {}: {:?}, took {:?} ",
      i,
      res.is_ok(),
      start.elapsed()
    );
    println!("[Secret key 1] Serialized size: {} bytes", bincode::serialize(&circuit_primary.new_sk).unwrap().len());
    println!("[Secret key 2] Serialized size: {} bytes", bincode::serialize(&recursive_snark).unwrap().len());
    //circuit_primary = circuit_primary.update_key();
//////////////////////////////////////////////////////
/*
    println!("test: {:#?}", recursive_snark);
    println!("old_sk: {:#?}", circuit_primary.old_sk);
    println!("new_sk: {:?}", circuit_primary.new_sk);
*/
    println!("old_sk: {:#?}", circuit_primary.old_sk);
    println!("new_sk: {:?}", circuit_primary.new_sk);
//////////////////////////////////////////////////////
  }

  // verify the recursive SNARK
  println!("Verifying a RecursiveSNARK...");
  let start = Instant::now();
  let res = recursive_snark.verify(&pp, num_steps, &z0_primary, &z0_secondary);
  println!("RecursiveSNARK::verify: {:?}, took {:?}", res.is_ok(), start.elapsed());
  assert!(res.is_ok());

  // produce the prover and verifier keys for compressed snark
  println!("Generating a CompressedSNARK using Spartan with IPA-PC...");
  let start = Instant::now();
  let (pk, vk) = CompressedSNARK::<E1, E2, C1, C2, S1, S2>::setup(&pp).unwrap();
  println!("CompressedSNARK::setup: took {:?}", start.elapsed());
  //serialized_data
  println!("Serialized size: {} bytes", bincode::serialize(&pk).unwrap().len());
  println!("Serialized size: {} bytes", bincode::serialize(&vk).unwrap().len());

  let start = Instant::now();


  // produce a compressed SNARK
  let res = CompressedSNARK::<E1, E2, C1, C2, S1, S2>::prove(&pp, &pk, &recursive_snark);
  println!("CompressedSNARK::prove: {:?}, took {:?}", res.is_ok(), start.elapsed());
  assert!(res.is_ok());
  let compressed_snark = res.unwrap();

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  //println!("ORIGINAL: {:?}", compressed_snark);
  let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
  bincode::serialize_into(&mut encoder, &compressed_snark).unwrap();
  let compressed_snark_encoded = encoder.finish().unwrap();
  println!("CompressedSNARK::len {:?} bytes", compressed_snark_encoded.len());
  //println!("TEST: {:?}", compressed_snark_encoded);

  use flate2::read::ZlibDecoder;
  use std::io::Read;
  let compressed_data = &compressed_snark_encoded[..];
  let mut decoder = ZlibDecoder::new(compressed_data);
  let mut decompressed_data = Vec::new();
  decoder.read_to_end(&mut decompressed_data).unwrap();

  let mut decompressed_snark: CompressedSNARK<E1, E2, C1, C2, S1, S2> = bincode::deserialize(&decompressed_data).unwrap();

  //serialized_data
  println!("[Signature 2] Serialized size: {} bytes", bincode::serialize(&compressed_snark).unwrap().len());
  //println!("DECOMP: {:?}", decompressed_snark);
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // verify the compressed SNARK
  println!("Verifying a CompressedSNARK...");
  let start = Instant::now();
  let res = decompressed_snark.verify(&vk, num_steps, &z0_primary, &z0_secondary);
  println!("CompressedSNARK::verify: {:?}, took {:?}", res.is_ok(), start.elapsed());
  assert!(res.is_ok());
  //println!("[Signature 1a] Serialized size: {} bytes", bincode::serialize(&z0_primary).unwrap().len());  
  //println!("[Signature 1b] Serialized size: {} bytes", bincode::serialize(&num_steps).unwrap().len());  
  println!("=========================================================");
  println!("=========================================================");
  println!("=========================================================");
  println!("=========================================================");
  println!("=========================================================");
  println!("=========================================================");
  println!("=========================================================");


  let start = Instant::now();
/*
  let circuit_sign = FSSNCircuitSign {
    pc2: pc.clone(),
    pc3: pc3.clone(),
    sk: <E1 as Engine>::Scalar::from(0),         // None
    period: <E1 as Engine>::Scalar::from(0),     // None
    vk: <E1 as Engine>::Scalar::from(0),         // None
    message: <E1 as Engine>::Scalar::from(0),    // None
  };
  let mut cs: ShapeCS<G1> = ShapeCS::new();
  let _ = circuit_sign.synthesize(&mut cs);
  let (r1cs_shape_sign, ck_sign) = cs.r1cs_shape();
*/
  let circuit_sign = FSSNCircuitSign::default();
  // produce keys
  let (pk, vk) = DirectSNARK::<E1, S, FSSNCircuitSign<<E1 as Engine>::Scalar>>::setup(circuit_sign.clone()).unwrap();
  println!("setup: took {:?}", start.elapsed());

  //serialized_data
  println!("Serialized size: {} bytes", bincode::serialize(&pk).unwrap().len());    //pk: SpartanProverKey<G1, EE1>
  println!("Serialized size: {} bytes", bincode::serialize(&vk).unwrap().len());    //vk: SpartanVerifierKey<G1, EE1>


  //println!("Number of constraints: {}", cs.num_constraints());  //r1cs_shape_sign.num_cons
  //println!("Number of inputs: {}", cs.num_inputs());
  //println!("Number of variables: {}", cs.num_aux());            //r1cs_shape_sign.num_vars

  // setup inputs
  let circuit_sign = FSSNCircuitSign {
    pc2: pc,
    pc3: pc3,
    sk: circuit_primary.new_sk,
    //period: <E1 as Engine>::Scalar::from(num_steps as u64),      //no guarantee in "usize == u32"
    //vk: z0_primary[0],
    message: <E1 as Engine>::Scalar::random(&mut rand::rngs::OsRng)
  };
  let ak = Poseidon::<<E1 as Engine>::Scalar, U2>::new_with_preimage(&[circuit_sign.sk, <E1 as Engine>::Scalar::from(AK_FLAG)], &circuit_sign.pc2).hash();
  let sig = Poseidon::<<E1 as Engine>::Scalar, U3>::new_with_preimage(&[<E1 as Engine>::Scalar::from(num_steps as u64), z0_primary[0], circuit_sign.message.clone()], &circuit_sign.pc3).hash();

  //let z = vec![<E1 as Engine>::Scalar::zero(), <E1 as Engine>::Scalar::zero()];
  let z = vec![z0_primary[0], <E1 as Engine>::Scalar::from(num_steps as u64), ak, sig];


  use std::mem;
  println!("SIZE OF Z {:?}", mem::size_of_val(&z[0]) * z.len());
  //println!("Serialized size: {} bytes", bincode::serialize(&z).unwrap().len());
  let start = Instant::now();
  // produce a SNARK
  let res = DirectSNARK::prove(&pk, circuit_sign.clone(), &z);
  assert!(res.is_ok());
  let output = circuit_sign.output(&z);
  let snark = res.unwrap();
  println!("prove: took {:?}", start.elapsed());

  //serialized_data
  println!("[Signature 4] Serialized size: {} bytes", bincode::serialize(&snark).unwrap().len());     //SNARK: DirectSNARK<G1, S, FSSNCircuitSign<<E1 as Engine>::Scalar>>

  let start = Instant::now();
  // verify the SNARK
  let io = z.clone().into_iter().chain(output.clone().into_iter()).collect::<Vec<_>>();
  let res = snark.verify(&vk, &io);
  assert!(res.is_ok());
  println!("verify: took {:?}", start.elapsed());
  //println!("[Signature 3] Serialized size: {} bytes", bincode::serialize(&io).unwrap().len());
  println!("[Signature 1,3] Serialized size: {} bytes", bincode::serialize(&ak).unwrap().len());
  println!("[Signature 1,3] Serialized size: {} bytes", bincode::serialize(&sig).unwrap().len());
  println!("[Verification key] Serialized size: {} bytes", bincode::serialize(&z0_primary[0]).unwrap().len());

  println!("input sk: {:?}", circuit_sign.sk);
  println!("output: {:?}", output);
  println!("message: {:?}", circuit_sign.message);

}