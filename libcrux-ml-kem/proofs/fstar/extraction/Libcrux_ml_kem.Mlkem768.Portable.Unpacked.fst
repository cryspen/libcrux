module Libcrux_ml_kem.Mlkem768.Portable.Unpacked
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Ind_cca.Unpacked in
  let open Libcrux_ml_kem.Vector.Portable in
  let open Libcrux_ml_kem.Vector.Portable.Vector_type in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

let key_pair_serialized_private_key
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 3)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  Libcrux_ml_kem.Ind_cca.Unpacked.impl_4__serialized_private_key (sz 3)
    #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
    (sz 1152)
    (sz 2400)
    (sz 1184)
    (sz 1152)
    key_pair

let key_pair_serialized_private_key_mut
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 3)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 2400))
     =
  let serialized:Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 2400) =
    Libcrux_ml_kem.Ind_cca.Unpacked.impl_4__serialized_private_key_mut (sz 3)
      #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (sz 1152)
      (sz 2400)
      (sz 1184)
      (sz 1152)
      key_pair
      serialized
  in
  serialized

let key_pair_serialized_public_key
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 3)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  Libcrux_ml_kem.Ind_cca.Unpacked.impl_4__serialized_public_key (sz 3)
    #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
    (sz 1152)
    (sz 1184)
    key_pair

let key_pair_serialized_public_key_mut
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 3)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1184))
     =
  let serialized:Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1184) =
    Libcrux_ml_kem.Ind_cca.Unpacked.impl_4__serialized_public_key_mut (sz 3)
      #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (sz 1152)
      (sz 1184)
      key_pair
      serialized
  in
  serialized

let serialized_public_key
      (public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 3)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1184))
     =
  let serialized:Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1184) =
    Libcrux_ml_kem.Ind_cca.Unpacked.impl_3__serialized_mut (sz 3)
      #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (sz 1152)
      (sz 1184)
      public_key
      serialized
  in
  serialized

let decapsulate
      (private_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 3)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1088))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Portable.Unpacked.decapsulate (sz 3) (sz 2400) (sz 1152)
    (sz 1184) (sz 1088) (sz 1152) (sz 960) (sz 128) (sz 10) (sz 4) (sz 320) (sz 2) (sz 128) (sz 2)
    (sz 128) (sz 1120) private_key ciphertext

let encapsulate
      (public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 3)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Portable.Unpacked.encapsulate (sz 3) (sz 1088) (sz 1184)
    (sz 1152) (sz 960) (sz 128) (sz 10) (sz 4) (sz 320) (sz 2) (sz 128) (sz 2) (sz 128) public_key
    randomness

let generate_key_pair_mut
      (randomness: t_Array u8 (sz 64))
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 3)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let key_pair:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 3)
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Ind_cca.Instantiations.Portable.Unpacked.generate_keypair (sz 3)
      (sz 1152)
      (sz 2400)
      (sz 1184)
      (sz 1152)
      (sz 2)
      (sz 128)
      randomness
      key_pair
  in
  key_pair

let generate_key_pair (randomness: t_Array u8 (sz 64)) =
  let key_pair:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 3)
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Core.Default.f_default #(Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 3)
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let key_pair:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 3)
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    generate_key_pair_mut randomness key_pair
  in
  key_pair

let init_key_pair (_: Prims.unit) =
  Core.Default.f_default #(Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 3)
        Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    #FStar.Tactics.Typeclasses.solve
    ()

let init_public_key (_: Prims.unit) =
  Core.Default.f_default #(Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 3)
        Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    #FStar.Tactics.Typeclasses.solve
    ()

let key_pair_from_private_mut
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 2400))
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 3)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let key_pair:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 3)
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Ind_cca.Instantiations.Portable.Unpacked.keypair_from_private_key (sz 3)
      (sz 2400)
      (sz 1152)
      (sz 1184)
      (sz 1152)
      (sz 1152)
      private_key
      key_pair
  in
  key_pair

let public_key
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 3)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (pk:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 3)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let pk:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 3)
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Core.Clone.f_clone #(Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 3)
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      #FStar.Tactics.Typeclasses.solve
      (Libcrux_ml_kem.Ind_cca.Unpacked.impl_4__public_key (sz 3)
          #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
          key_pair
        <:
        Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 3)
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  pk

let unpacked_public_key
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1184))
      (unpacked_public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 3)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let unpacked_public_key:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 3)
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Ind_cca.Instantiations.Portable.Unpacked.unpack_public_key (sz 3)
      (sz 1152)
      (sz 1152)
      (sz 1184)
      public_key
      unpacked_public_key
  in
  unpacked_public_key
