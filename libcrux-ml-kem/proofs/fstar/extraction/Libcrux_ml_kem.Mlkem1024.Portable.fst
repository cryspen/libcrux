module Libcrux_ml_kem.Mlkem1024.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let validate_private_key
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (Rust_primitives.mk_usize 3168))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (Rust_primitives.mk_usize 1568))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Portable.validate_private_key (Rust_primitives.mk_usize 4)
    (Rust_primitives.mk_usize 3168)
    (Rust_primitives.mk_usize 1568)
    private_key
    ciphertext

let decapsulate
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (Rust_primitives.mk_usize 3168))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (Rust_primitives.mk_usize 1568))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Portable.decapsulate (Rust_primitives.mk_usize 4)
    (Rust_primitives.mk_usize 3168) (Rust_primitives.mk_usize 1536) (Rust_primitives.mk_usize 1568)
    (Rust_primitives.mk_usize 1568) (Rust_primitives.mk_usize 1536) (Rust_primitives.mk_usize 1408)
    (Rust_primitives.mk_usize 160) (Rust_primitives.mk_usize 11) (Rust_primitives.mk_usize 5)
    (Rust_primitives.mk_usize 352) (Rust_primitives.mk_usize 2) (Rust_primitives.mk_usize 128)
    (Rust_primitives.mk_usize 2) (Rust_primitives.mk_usize 128) (Rust_primitives.mk_usize 1600)
    private_key ciphertext

let encapsulate
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (Rust_primitives.mk_usize 1568))
      (randomness: t_Array u8 (Rust_primitives.mk_usize 32))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Portable.encapsulate (Rust_primitives.mk_usize 4)
    (Rust_primitives.mk_usize 1568) (Rust_primitives.mk_usize 1568) (Rust_primitives.mk_usize 1536)
    (Rust_primitives.mk_usize 1408) (Rust_primitives.mk_usize 160) (Rust_primitives.mk_usize 11)
    (Rust_primitives.mk_usize 5) (Rust_primitives.mk_usize 352) (Rust_primitives.mk_usize 2)
    (Rust_primitives.mk_usize 128) (Rust_primitives.mk_usize 2) (Rust_primitives.mk_usize 128)
    public_key randomness

let generate_key_pair (randomness: t_Array u8 (Rust_primitives.mk_usize 64)) =
  Libcrux_ml_kem.Ind_cca.Instantiations.Portable.generate_keypair (Rust_primitives.mk_usize 4)
    (Rust_primitives.mk_usize 1536)
    (Rust_primitives.mk_usize 3168)
    (Rust_primitives.mk_usize 1568)
    (Rust_primitives.mk_usize 1536)
    (Rust_primitives.mk_usize 2)
    (Rust_primitives.mk_usize 128)
    randomness

let validate_public_key
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (Rust_primitives.mk_usize 1568))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Portable.validate_public_key (Rust_primitives.mk_usize 4)
    (Rust_primitives.mk_usize 1536)
    (Rust_primitives.mk_usize 1568)
    public_key.Libcrux_ml_kem.Types.f_value
