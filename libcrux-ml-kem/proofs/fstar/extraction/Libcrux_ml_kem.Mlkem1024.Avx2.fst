module Libcrux_ml_kem.Mlkem1024.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let validate_public_key (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 1568)) =
  Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.validate_public_key (mk_usize 4)
    (mk_usize 1536)
    (mk_usize 1568)
    public_key.Libcrux_ml_kem.Types.f_value

let validate_private_key
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 3168))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 1568))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.validate_private_key (mk_usize 4)
    (mk_usize 3168)
    (mk_usize 1568)
    private_key
    ciphertext

let validate_private_key_only (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 3168)) =
  Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.validate_private_key_only (mk_usize 4)
    (mk_usize 3168)
    private_key

let generate_key_pair (randomness: t_Array u8 (mk_usize 64)) =
  Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.generate_keypair (mk_usize 4)
    (mk_usize 1536)
    (mk_usize 3168)
    (mk_usize 1568)
    (mk_usize 1536)
    (mk_usize 2)
    (mk_usize 128)
    randomness

let encapsulate
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 1568))
      (randomness: t_Array u8 (mk_usize 32))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.encapsulate (mk_usize 4) (mk_usize 1568)
    (mk_usize 1568) (mk_usize 1536) (mk_usize 1408) (mk_usize 160) (mk_usize 11) (mk_usize 5)
    (mk_usize 352) (mk_usize 2) (mk_usize 128) (mk_usize 2) (mk_usize 128) public_key randomness

let decapsulate
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 3168))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 1568))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.decapsulate (mk_usize 4) (mk_usize 3168)
    (mk_usize 1536) (mk_usize 1568) (mk_usize 1568) (mk_usize 1536) (mk_usize 1408) (mk_usize 160)
    (mk_usize 11) (mk_usize 5) (mk_usize 352) (mk_usize 2) (mk_usize 128) (mk_usize 2)
    (mk_usize 128) (mk_usize 1600) private_key ciphertext
