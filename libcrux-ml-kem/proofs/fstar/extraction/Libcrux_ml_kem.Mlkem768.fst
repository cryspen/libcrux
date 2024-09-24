module Libcrux_ml_kem.Mlkem768
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let validate_private_key
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 2400))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1088))
     =
  Libcrux_ml_kem.Ind_cca.Multiplexing.validate_private_key (sz 3)
    (sz 2400)
    (sz 1088)
    private_key
    ciphertext

let validate_public_key (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1184)) =
  Libcrux_ml_kem.Ind_cca.Multiplexing.validate_public_key (sz 3)
    (sz 1152)
    (sz 1184)
    public_key.Libcrux_ml_kem.Types.f_value

let decapsulate
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 2400))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1088))
     =
  Libcrux_ml_kem.Ind_cca.Multiplexing.decapsulate (sz 3) (sz 2400) (sz 1152) (sz 1184) (sz 1088)
    (sz 1152) (sz 960) (sz 128) (sz 10) (sz 4) (sz 320) (sz 2) (sz 128) (sz 2) (sz 128) (sz 1120)
    private_key ciphertext

let encapsulate
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1184))
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_kem.Ind_cca.Multiplexing.encapsulate (sz 3) (sz 1088) (sz 1184) (sz 1152) (sz 960)
    (sz 128) (sz 10) (sz 4) (sz 320) (sz 2) (sz 128) (sz 2) (sz 128) public_key randomness

let generate_key_pair (randomness: t_Array u8 (sz 64)) =
  Libcrux_ml_kem.Ind_cca.Multiplexing.generate_keypair (sz 3)
    (sz 1152)
    (sz 2400)
    (sz 1184)
    (sz 1152)
    (sz 2)
    (sz 128)
    randomness
