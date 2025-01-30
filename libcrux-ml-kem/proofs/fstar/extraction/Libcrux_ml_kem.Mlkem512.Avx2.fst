module Libcrux_ml_kem.Mlkem512.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let validate_public_key (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 800)) =
  Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.validate_public_key (mk_usize 2)
    (mk_usize 768)
    (mk_usize 800)
    public_key.Libcrux_ml_kem.Types.f_value

let validate_private_key
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 1632))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 768))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.validate_private_key (mk_usize 2)
    (mk_usize 1632)
    (mk_usize 768)
    private_key
    ciphertext

let validate_private_key_only (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 1632)) =
  Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.validate_private_key_only (mk_usize 2)
    (mk_usize 1632)
    private_key

let generate_key_pair (randomness: t_Array u8 (mk_usize 64)) =
  Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.generate_keypair (mk_usize 2)
    (mk_usize 768)
    (mk_usize 1632)
    (mk_usize 800)
    (mk_usize 768)
    (mk_usize 3)
    (mk_usize 192)
    randomness

let encapsulate
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 800))
      (randomness: t_Array u8 (mk_usize 32))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.encapsulate (mk_usize 2) (mk_usize 768) (mk_usize 800)
    (mk_usize 768) (mk_usize 640) (mk_usize 128) (mk_usize 10) (mk_usize 4) (mk_usize 320)
    (mk_usize 3) (mk_usize 192) (mk_usize 2) (mk_usize 128) public_key randomness

let decapsulate
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 1632))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 768))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.decapsulate (mk_usize 2) (mk_usize 1632) (mk_usize 768)
    (mk_usize 800) (mk_usize 768) (mk_usize 768) (mk_usize 640) (mk_usize 128) (mk_usize 10)
    (mk_usize 4) (mk_usize 320) (mk_usize 3) (mk_usize 192) (mk_usize 2) (mk_usize 128)
    (mk_usize 800) private_key ciphertext
