module Libcrux_ml_dsa.Ml_dsa_44_.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let sign
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (Rust_primitives.mk_usize 2560))
      (message: t_Slice u8)
      (randomness: t_Array u8 (Rust_primitives.mk_usize 32))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.sign (Rust_primitives.mk_usize 4)
    (Rust_primitives.mk_usize 4) (Rust_primitives.mk_usize 2) (Rust_primitives.mk_usize 96)
    (Rust_primitives.mk_usize 17) (Rust_primitives.mk_i32 95232) (Rust_primitives.mk_usize 192)
    (Rust_primitives.mk_usize 768) (Rust_primitives.mk_usize 32) (Rust_primitives.mk_usize 39)
    (Rust_primitives.mk_usize 80) (Rust_primitives.mk_usize 576) (Rust_primitives.mk_usize 2560)
    (Rust_primitives.mk_usize 2420) signing_key.Libcrux_ml_dsa.Types._0 message randomness

let verify
      (verification_key:
          Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (Rust_primitives.mk_usize 1312))
      (message: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (Rust_primitives.mk_usize 2420))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.verify (Rust_primitives.mk_usize 4)
    (Rust_primitives.mk_usize 4) (Rust_primitives.mk_usize 2420) (Rust_primitives.mk_usize 1312)
    (Rust_primitives.mk_usize 17) (Rust_primitives.mk_usize 576) (Rust_primitives.mk_i32 95232)
    (Rust_primitives.mk_i32 78) (Rust_primitives.mk_usize 192) (Rust_primitives.mk_usize 768)
    (Rust_primitives.mk_usize 32) (Rust_primitives.mk_usize 39) (Rust_primitives.mk_usize 80)
    verification_key.Libcrux_ml_dsa.Types._0 message signature.Libcrux_ml_dsa.Types._0

let generate_key_pair (randomness: t_Array u8 (Rust_primitives.mk_usize 32)) =
  let signing_key, verification_key:(t_Array u8 (Rust_primitives.mk_usize 2560) &
    t_Array u8 (Rust_primitives.mk_usize 1312)) =
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.generate_key_pair (Rust_primitives.mk_usize 4)
      (Rust_primitives.mk_usize 4)
      (Rust_primitives.mk_usize 2)
      (Rust_primitives.mk_usize 96)
      (Rust_primitives.mk_usize 2560)
      (Rust_primitives.mk_usize 1312)
      randomness
  in
  {
    Libcrux_ml_dsa.Types.f_signing_key
    =
    Libcrux_ml_dsa.Types.MLDSASigningKey signing_key
    <:
    Libcrux_ml_dsa.Types.t_MLDSASigningKey (Rust_primitives.mk_usize 2560);
    Libcrux_ml_dsa.Types.f_verification_key
    =
    Libcrux_ml_dsa.Types.MLDSAVerificationKey verification_key
    <:
    Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (Rust_primitives.mk_usize 1312)
  }
  <:
  Libcrux_ml_dsa.Types.t_MLDSAKeyPair (Rust_primitives.mk_usize 1312)
    (Rust_primitives.mk_usize 2560)
