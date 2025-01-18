module Libcrux_ml_kem.Mlkem768
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let validate_private_key
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 2400))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 1088))
     =
  Libcrux_ml_kem.Ind_cca.Multiplexing.validate_private_key (mk_usize 3)
    (mk_usize 2400)
    (mk_usize 1088)
    private_key
    ciphertext

let validate_public_key (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 1184)) =
  Libcrux_ml_kem.Ind_cca.Multiplexing.validate_public_key (mk_usize 3)
    (mk_usize 1152)
    (mk_usize 1184)
    public_key.Libcrux_ml_kem.Types.f_value

let decapsulate
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 2400))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 1088))
     =
  let result:t_Array u8 (mk_usize 32) =
    Libcrux_ml_kem.Ind_cca.Multiplexing.decapsulate (mk_usize 3) (mk_usize 2400) (mk_usize 1152)
      (mk_usize 1184) (mk_usize 1088) (mk_usize 1152) (mk_usize 960) (mk_usize 128) (mk_usize 10)
      (mk_usize 4) (mk_usize 320) (mk_usize 2) (mk_usize 128) (mk_usize 2) (mk_usize 128)
      (mk_usize 1120) private_key ciphertext
  in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

let encapsulate
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 1184))
      (randomness: t_Array u8 (mk_usize 32))
     =
  let result:(Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 1088) & t_Array u8 (mk_usize 32)) =
    Libcrux_ml_kem.Ind_cca.Multiplexing.encapsulate (mk_usize 3) (mk_usize 1088) (mk_usize 1184)
      (mk_usize 1152) (mk_usize 960) (mk_usize 128) (mk_usize 10) (mk_usize 4) (mk_usize 320)
      (mk_usize 2) (mk_usize 128) (mk_usize 2) (mk_usize 128) public_key randomness
  in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

let generate_key_pair (randomness: t_Array u8 (mk_usize 64)) =
  let result:Libcrux_ml_kem.Types.t_MlKemKeyPair (mk_usize 2400) (mk_usize 1184) =
    Libcrux_ml_kem.Ind_cca.Multiplexing.generate_keypair (mk_usize 3)
      (mk_usize 1152)
      (mk_usize 2400)
      (mk_usize 1184)
      (mk_usize 1152)
      (mk_usize 2)
      (mk_usize 128)
      randomness
  in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result
