module Libcrux_ml_kem.Mlkem1024.Avx2.Unpacked
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Ind_cca.Unpacked in
  let open Libcrux_ml_kem.Vector.Avx2 in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

let key_pair_serialized_private_key
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 4)
            Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
     =
  Libcrux_ml_kem.Ind_cca.Unpacked.impl_4__serialized_private_key (sz 4)
    #Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector
    (sz 1536)
    (sz 3168)
    (sz 1568)
    (sz 1536)
    key_pair

let key_pair_serialized_private_key_mut
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 4)
            Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 3168))
     =
  let serialized:Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 3168) =
    Libcrux_ml_kem.Ind_cca.Unpacked.impl_4__serialized_private_key_mut (sz 4)
      #Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector
      (sz 1536)
      (sz 3168)
      (sz 1568)
      (sz 1536)
      key_pair
      serialized
  in
  serialized

let key_pair_serialized_public_key
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 4)
            Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
     =
  Libcrux_ml_kem.Ind_cca.Unpacked.impl_4__serialized_public_key (sz 4)
    #Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector
    (sz 1536)
    (sz 1568)
    key_pair

let key_pair_serialized_public_key_mut
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 4)
            Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1568))
     =
  let serialized:Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1568) =
    Libcrux_ml_kem.Ind_cca.Unpacked.impl_4__serialized_public_key_mut (sz 4)
      #Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector
      (sz 1536)
      (sz 1568)
      key_pair
      serialized
  in
  serialized

let serialized_public_key
      (public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 4)
            Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1568))
     =
  let serialized:Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1568) =
    Libcrux_ml_kem.Ind_cca.Unpacked.impl_3__serialized_mut (sz 4)
      #Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector
      (sz 1536)
      (sz 1568)
      public_key
      serialized
  in
  serialized

let decapsulate
      (private_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 4)
            Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1568))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.Unpacked.decapsulate (sz 4) (sz 3168) (sz 1536)
    (sz 1568) (sz 1568) (sz 1536) (sz 1408) (sz 160) (sz 11) (sz 5) (sz 352) (sz 2) (sz 128) (sz 2)
    (sz 128) (sz 1600) private_key ciphertext

let encapsulate
      (public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 4)
            Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.Unpacked.encapsulate (sz 4) (sz 1568) (sz 1568)
    (sz 1536) (sz 1408) (sz 160) (sz 11) (sz 5) (sz 352) (sz 2) (sz 128) (sz 2) (sz 128) public_key
    randomness

let generate_key_pair_mut
      (randomness: t_Array u8 (sz 64))
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 4)
            Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
     =
  let hax_temp_output, key_pair:(Prims.unit &
    Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 4)
      Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector) =
    (),
    Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.Unpacked.generate_keypair (sz 4)
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
        Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
  in
  key_pair

let generate_key_pair (randomness: t_Array u8 (sz 64)) =
  let key_pair:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 4)
    Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector =
    Core.Default.f_default #(Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 4)
          Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let key_pair:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 4)
    Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector =
    generate_key_pair_mut randomness key_pair
  in
  key_pair

let init_key_pair (_: Prims.unit) =
  Core.Default.f_default #(Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 4)
        Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
    #FStar.Tactics.Typeclasses.solve
    ()

let init_public_key (_: Prims.unit) =
  Core.Default.f_default #(Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 4)
        Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
    #FStar.Tactics.Typeclasses.solve
    ()

let key_pair_from_private_mut
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 3168))
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 4)
            Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
     =
  let key_pair:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 4)
    Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector =
    Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.Unpacked.keypair_from_private_key (sz 4)
      (sz 3168)
      (sz 1536)
      (sz 1568)
      (sz 1536)
      (sz 1536)
      private_key
      key_pair
  in
  key_pair

let unpacked_public_key
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1568))
      (unpacked_public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 4)
            Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
     =
  let hax_temp_output, unpacked_public_key:(Prims.unit &
    Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 4)
      Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector) =
    (),
    Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.Unpacked.unpack_public_key (sz 4)
      (sz 1536)
      (sz 1536)
      (sz 1568)
      public_key
      unpacked_public_key
    <:
    (Prims.unit &
      Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 4)
        Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector)
  in
  unpacked_public_key
