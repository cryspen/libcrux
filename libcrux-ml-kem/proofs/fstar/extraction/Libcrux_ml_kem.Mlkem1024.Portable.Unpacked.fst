module Libcrux_ml_kem.Mlkem1024.Portable.Unpacked
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Ind_cca.Unpacked in
  let open Libcrux_ml_kem.Vector.Portable in
  ()

let encapsulate
      (public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 4)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Portable.Unpacked.encapsulate (sz 4) (sz 1568) (sz 1568)
    (sz 1536) (sz 1408) (sz 160) (sz 11) (sz 5) (sz 352) (sz 2) (sz 128) (sz 2) (sz 128) public_key
    randomness

let init_public_key (_: Prims.unit) =
  Core.Default.f_default #(Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 4)
        Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    #FStar.Tactics.Typeclasses.solve
    ()

let serialized_public_key
      (public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 4)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1568))
     =
  let serialized:Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1568) =
    Libcrux_ml_kem.Ind_cca.Unpacked.impl__serialized_public_key_mut (sz 4)
      #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (sz 1536)
      (sz 1568)
      public_key
      serialized
  in
  serialized

let unpacked_public_key
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1568))
      (unpacked_public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 4)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let hax_temp_output, unpacked_public_key:(Prims.unit &
    Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 4)
      Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
    (),
    Libcrux_ml_kem.Ind_cca.Instantiations.Portable.Unpacked.unpack_public_key (sz 4)
      (sz 1536)
      (sz 1536)
      (sz 1568)
      public_key
      unpacked_public_key
    <:
    (Prims.unit &
      Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 4)
        Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  unpacked_public_key

let decapsulate
      (private_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 4)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1568))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Portable.Unpacked.decapsulate (sz 4) (sz 3168) (sz 1536)
    (sz 1568) (sz 1568) (sz 1536) (sz 1408) (sz 160) (sz 11) (sz 5) (sz 352) (sz 2) (sz 128) (sz 2)
    (sz 128) (sz 1600) private_key ciphertext

let generate_key_pair
      (randomness: t_Array u8 (sz 64))
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 4)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let hax_temp_output, key_pair:(Prims.unit &
    Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 4)
      Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
    (),
    Libcrux_ml_kem.Ind_cca.Instantiations.Portable.Unpacked.generate_keypair (sz 4)
      (sz 1536)
      (sz 3168)
      (sz 1568)
      (sz 1536)
      (sz 2)
      (sz 128)
      randomness
      key_pair
    <:
    (Prims.unit &
      Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 4)
        Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  key_pair

let init_key_pair (_: Prims.unit) =
  Core.Default.f_default #(Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 4)
        Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    #FStar.Tactics.Typeclasses.solve
    ()
