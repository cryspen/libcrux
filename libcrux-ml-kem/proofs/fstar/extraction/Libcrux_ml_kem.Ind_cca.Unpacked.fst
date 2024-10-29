module Libcrux_ml_kem.Ind_cca.Unpacked
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  let open Libcrux_ml_kem.Ind_cpa.Unpacked in
  let open Libcrux_ml_kem.Polynomial in
  let open Libcrux_ml_kem.Types in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

let impl__serialized_public_key
      (v_K: usize)
      (#v_Vector: Type0)
      (v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self: t_MlKemPublicKeyUnpacked v_K v_Vector)
     =
  Core.Convert.f_into #(t_Array u8 v_PUBLIC_KEY_SIZE)
    #(Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
    #FStar.Tactics.Typeclasses.solve
    (Libcrux_ml_kem.Ind_cpa.serialize_public_key v_K
        v_RANKED_BYTES_PER_RING_ELEMENT
        v_PUBLIC_KEY_SIZE
        #v_Vector
        self.f_ind_cpa_public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt
        (self.f_ind_cpa_public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_seed_for_A <: t_Slice u8)
      <:
      t_Array u8 v_PUBLIC_KEY_SIZE)

let impl__serialized_public_key_mut
      (v_K: usize)
      (#v_Vector: Type0)
      (v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self: t_MlKemPublicKeyUnpacked v_K v_Vector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
     =
  let serialized:Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE =
    {
      serialized with
      Libcrux_ml_kem.Types.f_value
      =
      Libcrux_ml_kem.Ind_cpa.serialize_public_key_mut v_K
        v_RANKED_BYTES_PER_RING_ELEMENT
        v_PUBLIC_KEY_SIZE
        #v_Vector
        self.f_ind_cpa_public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt
        (self.f_ind_cpa_public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_seed_for_A <: t_Slice u8)
        serialized.Libcrux_ml_kem.Types.f_value
    }
    <:
    Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE
  in
  serialized

let encapsulate
      (v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (public_key: t_MlKemPublicKeyUnpacked v_K v_Vector)
      (randomness: t_Array u8 (sz 32))
     =
  let (to_hash: t_Array u8 (sz 64)):t_Array u8 (sz 64) =
    Libcrux_ml_kem.Utils.into_padded_array (sz 64) (randomness <: t_Slice u8)
  in
  let to_hash:t_Array u8 (sz 64) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from to_hash
      ({ Core.Ops.Range.f_start = Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE }
        <:
        Core.Ops.Range.t_RangeFrom usize)
      (Core.Slice.impl__copy_from_slice #u8
          (to_hash.[ { Core.Ops.Range.f_start = Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE }
              <:
              Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          (public_key.f_public_key_hash <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let hashed:t_Array u8 (sz 64) =
    Libcrux_ml_kem.Hash_functions.f_G #v_Hasher
      #v_K
      #FStar.Tactics.Typeclasses.solve
      (to_hash <: t_Slice u8)
  in
  let shared_secret, pseudorandomness:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      (hashed <: t_Slice u8)
      Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE
  in
  let ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Libcrux_ml_kem.Ind_cpa.encrypt_unpacked v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE
      v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN
      v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE #v_Vector #v_Hasher
      public_key.f_ind_cpa_public_key randomness pseudorandomness
  in
  let shared_secret_array:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let shared_secret_array:t_Array u8 (sz 32) =
    Core.Slice.impl__copy_from_slice #u8 shared_secret_array shared_secret
  in
  Core.Convert.f_from #(Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
    #(t_Array u8 v_CIPHERTEXT_SIZE)
    #FStar.Tactics.Typeclasses.solve
    ciphertext,
  shared_secret_array
  <:
  (Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32))

let unpack_public_key
      (v_K v_T_AS_NTT_ENCODED_SIZE v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (#v_Hasher #v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (unpacked_public_key: t_MlKemPublicKeyUnpacked v_K v_Vector)
     =
  let unpacked_public_key:t_MlKemPublicKeyUnpacked v_K v_Vector =
    {
      unpacked_public_key with
      f_ind_cpa_public_key
      =
      {
        unpacked_public_key.f_ind_cpa_public_key with
        Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt
        =
        Libcrux_ml_kem.Serialize.deserialize_ring_elements_reduced v_T_AS_NTT_ENCODED_SIZE
          v_K
          #v_Vector
          (public_key.Libcrux_ml_kem.Types.f_value.[ {
                Core.Ops.Range.f_end = v_T_AS_NTT_ENCODED_SIZE
              }
              <:
              Core.Ops.Range.t_RangeTo usize ]
            <:
            t_Slice u8)
          unpacked_public_key.f_ind_cpa_public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt
      }
      <:
      Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector
    }
    <:
    t_MlKemPublicKeyUnpacked v_K v_Vector
  in
  let unpacked_public_key:t_MlKemPublicKeyUnpacked v_K v_Vector =
    {
      unpacked_public_key with
      f_ind_cpa_public_key
      =
      {
        unpacked_public_key.f_ind_cpa_public_key with
        Libcrux_ml_kem.Ind_cpa.Unpacked.f_seed_for_A
        =
        Libcrux_ml_kem.Utils.into_padded_array (sz 32)
          (public_key.Libcrux_ml_kem.Types.f_value.[ {
                Core.Ops.Range.f_start = v_T_AS_NTT_ENCODED_SIZE
              }
              <:
              Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
      }
      <:
      Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector
    }
    <:
    t_MlKemPublicKeyUnpacked v_K v_Vector
  in
  let unpacked_public_key:t_MlKemPublicKeyUnpacked v_K v_Vector =
    {
      unpacked_public_key with
      f_ind_cpa_public_key
      =
      {
        unpacked_public_key.f_ind_cpa_public_key with
        Libcrux_ml_kem.Ind_cpa.Unpacked.f_A
        =
        Libcrux_ml_kem.Matrix.sample_matrix_A v_K
          #v_Vector
          #v_Hasher
          unpacked_public_key.f_ind_cpa_public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_A
          (Libcrux_ml_kem.Utils.into_padded_array (sz 34)
              (public_key.Libcrux_ml_kem.Types.f_value.[ {
                    Core.Ops.Range.f_start = v_T_AS_NTT_ENCODED_SIZE
                  }
                  <:
                  Core.Ops.Range.t_RangeFrom usize ]
                <:
                t_Slice u8)
            <:
            t_Array u8 (sz 34))
          false
      }
      <:
      Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector
    }
    <:
    t_MlKemPublicKeyUnpacked v_K v_Vector
  in
  let unpacked_public_key:t_MlKemPublicKeyUnpacked v_K v_Vector =
    {
      unpacked_public_key with
      f_public_key_hash
      =
      Libcrux_ml_kem.Hash_functions.f_H #v_Hasher
        #v_K
        #FStar.Tactics.Typeclasses.solve
        (Libcrux_ml_kem.Types.impl_21__as_slice v_PUBLIC_KEY_SIZE public_key <: t_Slice u8)
    }
    <:
    t_MlKemPublicKeyUnpacked v_K v_Vector
  in
  unpacked_public_key

let impl_2__private_key
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self: t_MlKemKeyPairUnpacked v_K v_Vector)
     = self.f_private_key

let impl_2__public_key
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self: t_MlKemKeyPairUnpacked v_K v_Vector)
     = self.f_public_key

let impl_2__serialized_private_key
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self: t_MlKemKeyPairUnpacked v_K v_Vector)
     =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not yet implemented"
      <:
      Rust_primitives.Hax.t_Never)

let impl_2__serialized_public_key
      (v_K: usize)
      (#v_Vector: Type0)
      (v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self: t_MlKemKeyPairUnpacked v_K v_Vector)
     =
  impl__serialized_public_key v_K
    #v_Vector
    v_RANKED_BYTES_PER_RING_ELEMENT
    v_PUBLIC_KEY_SIZE
    self.f_public_key

let impl_2__serialized_public_key_mut
      (v_K: usize)
      (#v_Vector: Type0)
      (v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self: t_MlKemKeyPairUnpacked v_K v_Vector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
     =
  let hax_temp_output, serialized:(Prims.unit &
    Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE) =
    (),
    impl__serialized_public_key_mut v_K
      #v_Vector
      v_RANKED_BYTES_PER_RING_ELEMENT
      v_PUBLIC_KEY_SIZE
      self.f_public_key
      serialized
    <:
    (Prims.unit & Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
  in
  serialized

let impl_2__new
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (_: Prims.unit)
     =
  Core.Default.f_default #(t_MlKemKeyPairUnpacked v_K v_Vector) #FStar.Tactics.Typeclasses.solve ()

let decapsulate
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (key_pair: t_MlKemKeyPairUnpacked v_K v_Vector)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
     =
  let decrypted:t_Array u8 (sz 32) =
    Libcrux_ml_kem.Ind_cpa.decrypt_unpacked v_K
      v_CIPHERTEXT_SIZE
      v_C1_SIZE
      v_VECTOR_U_COMPRESSION_FACTOR
      v_VECTOR_V_COMPRESSION_FACTOR
      #v_Vector
      key_pair.f_private_key.f_ind_cpa_private_key
      ciphertext.Libcrux_ml_kem.Types.f_value
  in
  let (to_hash: t_Array u8 (sz 64)):t_Array u8 (sz 64) =
    Libcrux_ml_kem.Utils.into_padded_array (sz 64) (decrypted <: t_Slice u8)
  in
  let to_hash:t_Array u8 (sz 64) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from to_hash
      ({ Core.Ops.Range.f_start = Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE }
        <:
        Core.Ops.Range.t_RangeFrom usize)
      (Core.Slice.impl__copy_from_slice #u8
          (to_hash.[ { Core.Ops.Range.f_start = Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE }
              <:
              Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          (key_pair.f_public_key.f_public_key_hash <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let hashed:t_Array u8 (sz 64) =
    Libcrux_ml_kem.Hash_functions.f_G #v_Hasher
      #v_K
      #FStar.Tactics.Typeclasses.solve
      (to_hash <: t_Slice u8)
  in
  let shared_secret, pseudorandomness:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      (hashed <: t_Slice u8)
      Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE
  in
  let (to_hash: t_Array u8 v_IMPLICIT_REJECTION_HASH_INPUT_SIZE):t_Array u8
    v_IMPLICIT_REJECTION_HASH_INPUT_SIZE =
    Libcrux_ml_kem.Utils.into_padded_array v_IMPLICIT_REJECTION_HASH_INPUT_SIZE
      (key_pair.f_private_key.f_implicit_rejection_value <: t_Slice u8)
  in
  let to_hash:t_Array u8 v_IMPLICIT_REJECTION_HASH_INPUT_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from to_hash
      ({ Core.Ops.Range.f_start = Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE }
        <:
        Core.Ops.Range.t_RangeFrom usize)
      (Core.Slice.impl__copy_from_slice #u8
          (to_hash.[ { Core.Ops.Range.f_start = Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE }
              <:
              Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          (Core.Convert.f_as_ref #(Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
              #(t_Slice u8)
              #FStar.Tactics.Typeclasses.solve
              ciphertext
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let (implicit_rejection_shared_secret: t_Array u8 (sz 32)):t_Array u8 (sz 32) =
    Libcrux_ml_kem.Hash_functions.f_PRF #v_Hasher
      #v_K
      #FStar.Tactics.Typeclasses.solve
      (sz 32)
      (to_hash <: t_Slice u8)
  in
  let expected_ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Libcrux_ml_kem.Ind_cpa.encrypt_unpacked v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE
      v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1
      v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE #v_Vector #v_Hasher
      key_pair.f_public_key.f_ind_cpa_public_key decrypted pseudorandomness
  in
  let selector:u8 =
    Libcrux_ml_kem.Constant_time_ops.compare_ciphertexts_in_constant_time (Core.Convert.f_as_ref #(Libcrux_ml_kem.Types.t_MlKemCiphertext
            v_CIPHERTEXT_SIZE)
          #(t_Slice u8)
          #FStar.Tactics.Typeclasses.solve
          ciphertext
        <:
        t_Slice u8)
      (expected_ciphertext <: t_Slice u8)
  in
  Libcrux_ml_kem.Constant_time_ops.select_shared_secret_in_constant_time shared_secret
    (implicit_rejection_shared_secret <: t_Slice u8)
    selector

let generate_keypair
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (randomness: t_Array u8 (sz 64))
      (out: t_MlKemKeyPairUnpacked v_K v_Vector)
     =
  let ind_cpa_keypair_randomness:t_Slice u8 =
    randomness.[ {
        Core.Ops.Range.f_start = sz 0;
        Core.Ops.Range.f_end = Libcrux_ml_kem.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
      }
      <:
      Core.Ops.Range.t_Range usize ]
  in
  let implicit_rejection_value:t_Slice u8 =
    randomness.[ {
        Core.Ops.Range.f_start = Libcrux_ml_kem.Constants.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
      }
      <:
      Core.Ops.Range.t_RangeFrom usize ]
  in
  let tmp0, tmp1:(Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector &
    Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector) =
    Libcrux_ml_kem.Ind_cpa.generate_keypair_unpacked v_K
      v_ETA1
      v_ETA1_RANDOMNESS_SIZE
      #v_Vector
      #v_Hasher
      ind_cpa_keypair_randomness
      out.f_private_key.f_ind_cpa_private_key
      out.f_public_key.f_ind_cpa_public_key
  in
  let out:t_MlKemKeyPairUnpacked v_K v_Vector =
    {
      out with
      f_private_key
      =
      { out.f_private_key with f_ind_cpa_private_key = tmp0 }
      <:
      t_MlKemPrivateKeyUnpacked v_K v_Vector
    }
    <:
    t_MlKemKeyPairUnpacked v_K v_Vector
  in
  let out:t_MlKemKeyPairUnpacked v_K v_Vector =
    {
      out with
      f_public_key
      =
      { out.f_public_key with f_ind_cpa_public_key = tmp1 } <: t_MlKemPublicKeyUnpacked v_K v_Vector
    }
    <:
    t_MlKemKeyPairUnpacked v_K v_Vector
  in
  let _:Prims.unit = () in
  let v_A:t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
    Core.Array.from_fn #(t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      v_K
      (fun v__i ->
          let v__i:usize = v__i in
          Core.Array.from_fn #(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
            v_K
            (fun v__j ->
                let v__j:usize = v__j in
                Libcrux_ml_kem.Polynomial.impl__ZERO #v_Vector ()
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          <:
          t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
  in
  let v_A:t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_K
      (fun v_A temp_1_ ->
          let v_A:t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
            v_K =
            v_A
          in
          let _:usize = temp_1_ in
          true)
      v_A
      (fun v_A i ->
          let v_A:t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
            v_K =
            v_A
          in
          let i:usize = i in
          Rust_primitives.Hax.Folds.fold_range (sz 0)
            v_K
            (fun v_A temp_1_ ->
                let v_A:t_Array
                  (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
                  v_A
                in
                let _:usize = temp_1_ in
                true)
            v_A
            (fun v_A j ->
                let v_A:t_Array
                  (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
                  v_A
                in
                let j:usize = j in
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A
                  i
                  (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A.[ i ]
                        <:
                        t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
                      j
                      (Core.Clone.f_clone #(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
                            v_Vector)
                          #FStar.Tactics.Typeclasses.solve
                          ((out.f_public_key.f_ind_cpa_public_key
                                .Libcrux_ml_kem.Ind_cpa.Unpacked.f_A.[ j ]
                              <:
                              t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                                v_K).[ i ]
                            <:
                            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                        <:
                        Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                    <:
                    t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
                <:
                t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
                  v_K)
          <:
          t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K)
  in
  let out:t_MlKemKeyPairUnpacked v_K v_Vector =
    {
      out with
      f_public_key
      =
      {
        out.f_public_key with
        f_ind_cpa_public_key
        =
        { out.f_public_key.f_ind_cpa_public_key with Libcrux_ml_kem.Ind_cpa.Unpacked.f_A = v_A }
        <:
        Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector
      }
      <:
      t_MlKemPublicKeyUnpacked v_K v_Vector
    }
    <:
    t_MlKemKeyPairUnpacked v_K v_Vector
  in
  let pk_serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    Libcrux_ml_kem.Ind_cpa.serialize_public_key v_K
      v_BYTES_PER_RING_ELEMENT
      v_PUBLIC_KEY_SIZE
      #v_Vector
      out.f_public_key.f_ind_cpa_public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt
      (out.f_public_key.f_ind_cpa_public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_seed_for_A
        <:
        t_Slice u8)
  in
  let out:t_MlKemKeyPairUnpacked v_K v_Vector =
    {
      out with
      f_public_key
      =
      {
        out.f_public_key with
        f_public_key_hash
        =
        Libcrux_ml_kem.Hash_functions.f_H #v_Hasher
          #v_K
          #FStar.Tactics.Typeclasses.solve
          (pk_serialized <: t_Slice u8)
      }
      <:
      t_MlKemPublicKeyUnpacked v_K v_Vector
    }
    <:
    t_MlKemKeyPairUnpacked v_K v_Vector
  in
  let out:t_MlKemKeyPairUnpacked v_K v_Vector =
    {
      out with
      f_private_key
      =
      {
        out.f_private_key with
        f_implicit_rejection_value
        =
        Core.Result.impl__unwrap #(t_Array u8 (sz 32))
          #Core.Array.t_TryFromSliceError
          (Core.Convert.f_try_into #(t_Slice u8)
              #(t_Array u8 (sz 32))
              #FStar.Tactics.Typeclasses.solve
              implicit_rejection_value
            <:
            Core.Result.t_Result (t_Array u8 (sz 32)) Core.Array.t_TryFromSliceError)
      }
      <:
      t_MlKemPrivateKeyUnpacked v_K v_Vector
    }
    <:
    t_MlKemKeyPairUnpacked v_K v_Vector
  in
  out
