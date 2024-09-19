module Libcrux_ml_kem.Mlkem512.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let decapsulate
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 1632))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 768))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Neon.decapsulate (sz 2) (sz 1632) (sz 768) (sz 800) (sz 768)
    (sz 768) (sz 640) (sz 128) (sz 10) (sz 4) (sz 320) (sz 3) (sz 192) (sz 2) (sz 128) (sz 800)
    private_key ciphertext

let encapsulate
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 800))
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Neon.encapsulate (sz 2) (sz 768) (sz 800) (sz 768) (sz 640)
    (sz 128) (sz 10) (sz 4) (sz 320) (sz 3) (sz 192) (sz 2) (sz 128) public_key randomness

let generate_key_pair (randomness: t_Array u8 (sz 64)) =
  Libcrux_ml_kem.Ind_cca.Instantiations.Neon.generate_keypair (sz 2)
    (sz 768)
    (sz 1632)
    (sz 800)
    (sz 768)
    (sz 3)
    (sz 192)
    randomness

let validate_public_key (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 800)) =
  if
    Libcrux_ml_kem.Ind_cca.Instantiations.Neon.validate_public_key (sz 2)
      (sz 768)
      (sz 800)
      public_key.Libcrux_ml_kem.Types.f_value
  then
    Core.Option.Option_Some public_key
    <:
    Core.Option.t_Option (Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 800))
  else
    Core.Option.Option_None <: Core.Option.t_Option (Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 800))

let encapsulate_unpacked
      (public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 2)
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Neon.encapsulate_unpacked (sz 2) (sz 768) (sz 800) (sz 768)
    (sz 640) (sz 128) (sz 10) (sz 4) (sz 320) (sz 3) (sz 192) (sz 2) (sz 128) public_key randomness

let decapsulate_unpacked
      (private_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 2)
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 768))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Neon.decapsulate_unpacked (sz 2) (sz 1632) (sz 768) (sz 800)
    (sz 768) (sz 768) (sz 640) (sz 128) (sz 10) (sz 4) (sz 320) (sz 3) (sz 192) (sz 2) (sz 128)
    (sz 800) private_key ciphertext

let generate_key_pair_unpacked (randomness: t_Array u8 (sz 64)) =
  Libcrux_ml_kem.Ind_cca.Instantiations.Neon.generate_keypair_unpacked (sz 2)
    (sz 768)
    (sz 1632)
    (sz 800)
    (sz 768)
    (sz 3)
    (sz 192)
    randomness
