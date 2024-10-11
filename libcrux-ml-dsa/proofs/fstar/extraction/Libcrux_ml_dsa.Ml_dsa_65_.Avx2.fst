module Libcrux_ml_dsa.Ml_dsa_65_.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let sign
      (signing_key: Libcrux_ml_dsa.Types.t_MLDSASigningKey (Rust_primitives.mk_usize 4032))
      (message: t_Slice u8)
      (randomness: t_Array u8 (Rust_primitives.mk_usize 32))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.sign (Rust_primitives.mk_usize 6)
    (Rust_primitives.mk_usize 5) (Rust_primitives.mk_usize 4) (Rust_primitives.mk_usize 128)
    (Rust_primitives.mk_usize 19) (Rust_primitives.mk_i32 261888) (Rust_primitives.mk_usize 128)
    (Rust_primitives.mk_usize 768) (Rust_primitives.mk_usize 48) (Rust_primitives.mk_usize 49)
    (Rust_primitives.mk_usize 55) (Rust_primitives.mk_usize 640) (Rust_primitives.mk_usize 4032)
    (Rust_primitives.mk_usize 3309) signing_key.Libcrux_ml_dsa.Types._0 message randomness

let verify
      (verification_key:
          Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (Rust_primitives.mk_usize 1952))
      (message: t_Slice u8)
      (signature: Libcrux_ml_dsa.Types.t_MLDSASignature (Rust_primitives.mk_usize 3309))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.verify (Rust_primitives.mk_usize 6)
    (Rust_primitives.mk_usize 5) (Rust_primitives.mk_usize 3309) (Rust_primitives.mk_usize 1952)
    (Rust_primitives.mk_usize 19) (Rust_primitives.mk_usize 640) (Rust_primitives.mk_i32 261888)
    (Rust_primitives.mk_i32 196) (Rust_primitives.mk_usize 128) (Rust_primitives.mk_usize 768)
    (Rust_primitives.mk_usize 48) (Rust_primitives.mk_usize 49) (Rust_primitives.mk_usize 55)
    verification_key.Libcrux_ml_dsa.Types._0 message signature.Libcrux_ml_dsa.Types._0

let generate_key_pair (randomness: t_Array u8 (Rust_primitives.mk_usize 32)) =
  let signing_key, verification_key:(t_Array u8 (Rust_primitives.mk_usize 4032) &
    t_Array u8 (Rust_primitives.mk_usize 1952)) =
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.generate_key_pair (Rust_primitives.mk_usize 6)
      (Rust_primitives.mk_usize 5)
      (Rust_primitives.mk_usize 4)
      (Rust_primitives.mk_usize 128)
      (Rust_primitives.mk_usize 4032)
      (Rust_primitives.mk_usize 1952)
      randomness
  in
  {
    Libcrux_ml_dsa.Types.f_signing_key
    =
    Libcrux_ml_dsa.Types.MLDSASigningKey signing_key
    <:
    Libcrux_ml_dsa.Types.t_MLDSASigningKey (Rust_primitives.mk_usize 4032);
    Libcrux_ml_dsa.Types.f_verification_key
    =
    Libcrux_ml_dsa.Types.MLDSAVerificationKey verification_key
    <:
    Libcrux_ml_dsa.Types.t_MLDSAVerificationKey (Rust_primitives.mk_usize 1952)
  }
  <:
  Libcrux_ml_dsa.Types.t_MLDSAKeyPair (Rust_primitives.mk_usize 1952)
    (Rust_primitives.mk_usize 4032)
