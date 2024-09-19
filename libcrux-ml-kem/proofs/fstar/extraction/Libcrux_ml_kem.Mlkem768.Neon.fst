module Libcrux_ml_kem.Mlkem768.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let decapsulate
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 2400))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1088))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Neon.decapsulate (sz 3) (sz 2400) (sz 1152) (sz 1184)
    (sz 1088) (sz 1152) (sz 960) (sz 128) (sz 10) (sz 4) (sz 320) (sz 2) (sz 128) (sz 2) (sz 128)
    (sz 1120) private_key ciphertext

let encapsulate
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1184))
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Neon.encapsulate (sz 3) (sz 1088) (sz 1184) (sz 1152)
    (sz 960) (sz 128) (sz 10) (sz 4) (sz 320) (sz 2) (sz 128) (sz 2) (sz 128) public_key randomness

let generate_key_pair (randomness: t_Array u8 (sz 64)) =
  Libcrux_ml_kem.Ind_cca.Instantiations.Neon.generate_keypair (sz 3)
    (sz 1152)
    (sz 2400)
    (sz 1184)
    (sz 1152)
    (sz 2)
    (sz 128)
    randomness

let validate_public_key (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1184)) =
  if
    Libcrux_ml_kem.Ind_cca.Instantiations.Neon.validate_public_key (sz 3)
      (sz 1152)
      (sz 1184)
      public_key.Libcrux_ml_kem.Types.f_value
  then
    Core.Option.Option_Some public_key
    <:
    Core.Option.t_Option (Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1184))
  else
    Core.Option.Option_None
    <:
    Core.Option.t_Option (Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1184))

let encapsulate_unpacked
      (public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 3)
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Neon.encapsulate_unpacked (sz 3) (sz 1088) (sz 1184)
    (sz 1152) (sz 960) (sz 128) (sz 10) (sz 4) (sz 320) (sz 2) (sz 128) (sz 2) (sz 128) public_key
    randomness

let decapsulate_unpacked
      (private_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 3)
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1088))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Neon.decapsulate_unpacked (sz 3) (sz 2400) (sz 1152)
    (sz 1184) (sz 1088) (sz 1152) (sz 960) (sz 128) (sz 10) (sz 4) (sz 320) (sz 2) (sz 128) (sz 2)
    (sz 128) (sz 1120) private_key ciphertext

let generate_key_pair_unpacked (randomness: t_Array u8 (sz 64)) =
  Libcrux_ml_kem.Ind_cca.Instantiations.Neon.generate_keypair_unpacked (sz 3)
    (sz 1152)
    (sz 2400)
    (sz 1184)
    (sz 1152)
    (sz 2)
    (sz 128)
    randomness
