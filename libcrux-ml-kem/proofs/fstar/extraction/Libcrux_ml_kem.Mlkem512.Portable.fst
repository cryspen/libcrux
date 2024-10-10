module Libcrux_ml_kem.Mlkem512.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let validate_private_key
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (Rust_primitives.mk_usize 1632))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (Rust_primitives.mk_usize 768))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Portable.validate_private_key (Rust_primitives.mk_usize 2)
    (Rust_primitives.mk_usize 1632)
    (Rust_primitives.mk_usize 768)
    private_key
    ciphertext

let decapsulate
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (Rust_primitives.mk_usize 1632))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (Rust_primitives.mk_usize 768))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Portable.decapsulate (Rust_primitives.mk_usize 2)
    (Rust_primitives.mk_usize 1632) (Rust_primitives.mk_usize 768) (Rust_primitives.mk_usize 800)
    (Rust_primitives.mk_usize 768) (Rust_primitives.mk_usize 768) (Rust_primitives.mk_usize 640)
    (Rust_primitives.mk_usize 128) (Rust_primitives.mk_usize 10) (Rust_primitives.mk_usize 4)
    (Rust_primitives.mk_usize 320) (Rust_primitives.mk_usize 3) (Rust_primitives.mk_usize 192)
    (Rust_primitives.mk_usize 2) (Rust_primitives.mk_usize 128) (Rust_primitives.mk_usize 800)
    private_key ciphertext

let encapsulate
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (Rust_primitives.mk_usize 800))
      (randomness: t_Array u8 (Rust_primitives.mk_usize 32))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Portable.encapsulate (Rust_primitives.mk_usize 2)
    (Rust_primitives.mk_usize 768) (Rust_primitives.mk_usize 800) (Rust_primitives.mk_usize 768)
    (Rust_primitives.mk_usize 640) (Rust_primitives.mk_usize 128) (Rust_primitives.mk_usize 10)
    (Rust_primitives.mk_usize 4) (Rust_primitives.mk_usize 320) (Rust_primitives.mk_usize 3)
    (Rust_primitives.mk_usize 192) (Rust_primitives.mk_usize 2) (Rust_primitives.mk_usize 128)
    public_key randomness

let generate_key_pair (randomness: t_Array u8 (Rust_primitives.mk_usize 64)) =
  Libcrux_ml_kem.Ind_cca.Instantiations.Portable.generate_keypair (Rust_primitives.mk_usize 2)
    (Rust_primitives.mk_usize 768)
    (Rust_primitives.mk_usize 1632)
    (Rust_primitives.mk_usize 800)
    (Rust_primitives.mk_usize 768)
    (Rust_primitives.mk_usize 3)
    (Rust_primitives.mk_usize 192)
    randomness

let validate_public_key
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (Rust_primitives.mk_usize 800))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Portable.validate_public_key (Rust_primitives.mk_usize 2)
    (Rust_primitives.mk_usize 768)
    (Rust_primitives.mk_usize 800)
    public_key.Libcrux_ml_kem.Types.f_value
