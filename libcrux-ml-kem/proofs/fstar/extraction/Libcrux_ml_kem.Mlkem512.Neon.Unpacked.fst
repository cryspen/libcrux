module Libcrux_ml_kem.Mlkem512.Neon.Unpacked
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Ind_cca.Unpacked in
  let open Libcrux_ml_kem.Vector.Neon in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

let init_key_pair (_: Prims.unit) =
  Core.Default.f_default #(Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 2)
        Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
    #FStar.Tactics.Typeclasses.solve
    ()

let init_public_key (_: Prims.unit) =
  Core.Default.f_default #(Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (mk_usize 2)
        Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
    #FStar.Tactics.Typeclasses.solve
    ()

let serialized_public_key
      (public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (mk_usize 2)
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 800))
     =
  let serialized:Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 800) =
    Libcrux_ml_kem.Ind_cca.Unpacked.impl_3__serialized_mut (mk_usize 2)
      #Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      (mk_usize 800)
      public_key
      serialized
  in
  serialized

let key_pair_serialized_private_key
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 2)
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
     =
  Libcrux_ml_kem.Ind_cca.Unpacked.impl_4__serialized_private_key (mk_usize 2)
    #Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
    (mk_usize 768)
    (mk_usize 1632)
    (mk_usize 800)
    key_pair

let key_pair_serialized_private_key_mut
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 2)
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 1632))
     =
  let serialized:Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 1632) =
    Libcrux_ml_kem.Ind_cca.Unpacked.impl_4__serialized_private_key_mut (mk_usize 2)
      #Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      (mk_usize 768)
      (mk_usize 1632)
      (mk_usize 800)
      key_pair
      serialized
  in
  serialized

let key_pair_serialized_public_key_mut
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 2)
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 800))
     =
  let serialized:Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 800) =
    Libcrux_ml_kem.Ind_cca.Unpacked.impl_4__serialized_public_key_mut (mk_usize 2)
      #Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      (mk_usize 800)
      key_pair
      serialized
  in
  serialized

let key_pair_serialized_public_key
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 2)
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
     =
  Libcrux_ml_kem.Ind_cca.Unpacked.impl_4__serialized_public_key (mk_usize 2)
    #Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
    (mk_usize 800)
    key_pair

let key_pair_from_private_mut
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 1632))
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 2)
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
     =
  let key_pair:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 2)
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    Libcrux_ml_kem.Ind_cca.Instantiations.Neon.Unpacked.keypair_from_private_key (mk_usize 2)
      (mk_usize 1632)
      (mk_usize 768)
      (mk_usize 800)
      (mk_usize 768)
      private_key
      key_pair
  in
  key_pair

let unpacked_public_key
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 800))
      (unpacked_public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (mk_usize 2)
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
     =
  let unpacked_public_key:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (mk_usize 2)
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    Libcrux_ml_kem.Ind_cca.Instantiations.Neon.Unpacked.unpack_public_key (mk_usize 2)
      (mk_usize 768)
      (mk_usize 800)
      public_key
      unpacked_public_key
  in
  unpacked_public_key

let generate_key_pair_mut
      (randomness: t_Array u8 (mk_usize 64))
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 2)
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
     =
  let key_pair:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 2)
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    Libcrux_ml_kem.Ind_cca.Instantiations.Neon.Unpacked.generate_keypair (mk_usize 2)
      (mk_usize 768)
      (mk_usize 1632)
      (mk_usize 800)
      (mk_usize 3)
      (mk_usize 192)
      randomness
      key_pair
  in
  key_pair

let generate_key_pair (randomness: t_Array u8 (mk_usize 64)) =
  let key_pair:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 2)
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    Core.Default.f_default #(Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 2)
          Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let key_pair:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 2)
    Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
    generate_key_pair_mut randomness key_pair
  in
  key_pair

let encapsulate
      (public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (mk_usize 2)
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (randomness: t_Array u8 (mk_usize 32))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Neon.Unpacked.encapsulate (mk_usize 2) (mk_usize 768)
    (mk_usize 800) (mk_usize 768) (mk_usize 640) (mk_usize 128) (mk_usize 10) (mk_usize 4)
    (mk_usize 320) (mk_usize 3) (mk_usize 192) (mk_usize 2) (mk_usize 128) public_key randomness

let decapsulate
      (private_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 2)
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 768))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Neon.Unpacked.decapsulate (mk_usize 2) (mk_usize 1632)
    (mk_usize 768) (mk_usize 800) (mk_usize 768) (mk_usize 768) (mk_usize 640) (mk_usize 128)
    (mk_usize 10) (mk_usize 4) (mk_usize 320) (mk_usize 3) (mk_usize 192) (mk_usize 2)
    (mk_usize 128) (mk_usize 800) private_key ciphertext
