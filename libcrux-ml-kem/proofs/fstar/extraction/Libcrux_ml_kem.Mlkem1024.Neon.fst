module Libcrux_ml_kem.Mlkem1024.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let validate_private_key
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 3168))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1568))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Neon.validate_private_key (sz 4)
    (sz 3168)
    (sz 1568)
    private_key
    ciphertext

let validate_private_key_only (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 3168)) =
  Libcrux_ml_kem.Ind_cca.Instantiations.Neon.validate_private_key_only (sz 4) (sz 3168) private_key

let decapsulate
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 3168))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1568))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Neon.decapsulate (sz 4) (sz 3168) (sz 1536) (sz 1568)
    (sz 1568) (sz 1536) (sz 1408) (sz 160) (sz 11) (sz 5) (sz 352) (sz 2) (sz 128) (sz 2) (sz 128)
    (sz 1600) private_key ciphertext

let encapsulate
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1568))
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Neon.encapsulate (sz 4) (sz 1568) (sz 1568) (sz 1536)
    (sz 1408) (sz 160) (sz 11) (sz 5) (sz 352) (sz 2) (sz 128) (sz 2) (sz 128) public_key randomness

let generate_key_pair (randomness: t_Array u8 (sz 64)) =
  Libcrux_ml_kem.Ind_cca.Instantiations.Neon.generate_keypair (sz 4)
    (sz 1536)
    (sz 3168)
    (sz 1568)
    (sz 1536)
    (sz 2)
    (sz 128)
    randomness

let validate_public_key (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1568)) =
  Libcrux_ml_kem.Ind_cca.Instantiations.Neon.validate_public_key (sz 4)
    (sz 1536)
    (sz 1568)
    public_key.Libcrux_ml_kem.Types.f_value
