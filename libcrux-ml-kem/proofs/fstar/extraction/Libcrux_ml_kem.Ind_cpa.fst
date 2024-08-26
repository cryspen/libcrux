module Libcrux_ml_kem.Ind_cpa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

let sample_ring_element_cbd
      (v_K v_ETA2_RANDOMNESS_SIZE v_ETA2: usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8)
     =
  let error_1_:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core.Array.from_fn #(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
      (fun v__i ->
          let v__i:usize = v__i in
          Libcrux_ml_kem.Polynomial.impl_1__ZERO #v_Vector ()
          <:
          Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let prf_inputs:t_Array (t_Array u8 (sz 33)) v_K = Rust_primitives.Hax.repeat prf_input v_K in
  let v__domain_separator_init:u8 = domain_separator in
  let domain_separator, prf_inputs:(u8 & t_Array (t_Array u8 (sz 33)) v_K) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_K
      (fun temp_0_ i ->
          let domain_separator, prf_inputs:(u8 & t_Array (t_Array u8 (sz 33)) v_K) = temp_0_ in
          let i:usize = i in
          v domain_separator == v v__domain_separator_init + v i)
      (domain_separator, prf_inputs <: (u8 & t_Array (t_Array u8 (sz 33)) v_K))
      (fun temp_0_ i ->
          let domain_separator, prf_inputs:(u8 & t_Array (t_Array u8 (sz 33)) v_K) = temp_0_ in
          let i:usize = i in
          let prf_inputs:t_Array (t_Array u8 (sz 33)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize prf_inputs
              i
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (prf_inputs.[ i ]
                    <:
                    t_Array u8 (sz 33))
                  (sz 32)
                  domain_separator
                <:
                t_Array u8 (sz 33))
          in
          let domain_separator:u8 = domain_separator +! 1uy in
          domain_separator, prf_inputs <: (u8 & t_Array (t_Array u8 (sz 33)) v_K))
  in
  let (prf_outputs: t_Array (t_Array u8 v_ETA2_RANDOMNESS_SIZE) v_K):t_Array
    (t_Array u8 v_ETA2_RANDOMNESS_SIZE) v_K =
    Libcrux_ml_kem.Hash_functions.f_PRFxN #v_Hasher
      #v_K
      #FStar.Tactics.Typeclasses.solve
      v_ETA2_RANDOMNESS_SIZE
      prf_inputs
  in
  let error_1_:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_K
      (fun error_1_ temp_1_ ->
          let error_1_:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            error_1_
          in
          let _:usize = temp_1_ in
          true)
      error_1_
      (fun error_1_ i ->
          let error_1_:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            error_1_
          in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize error_1_
            i
            (Libcrux_ml_kem.Sampling.sample_from_binomial_distribution v_ETA2
                #v_Vector
                (prf_outputs.[ i ] <: t_Slice u8)
              <:
              Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          <:
          t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
  in
  let result:(t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K & u8) =
    error_1_, domain_separator
    <:
    (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K & u8)
  in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

let sample_vector_cbd_then_ntt
      (v_K v_ETA v_ETA_RANDOMNESS_SIZE: usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8)
     =
  let re_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core.Array.from_fn #(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
      (fun v__i ->
          let v__i:usize = v__i in
          Libcrux_ml_kem.Polynomial.impl_1__ZERO #v_Vector ()
          <:
          Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let prf_inputs:t_Array (t_Array u8 (sz 33)) v_K = Rust_primitives.Hax.repeat prf_input v_K in
  let v__domain_separator_init:u8 = domain_separator in
  let domain_separator, prf_inputs:(u8 & t_Array (t_Array u8 (sz 33)) v_K) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_K
      (fun temp_0_ i ->
          let domain_separator, prf_inputs:(u8 & t_Array (t_Array u8 (sz 33)) v_K) = temp_0_ in
          let i:usize = i in
          v domain_separator == v v__domain_separator_init + v i)
      (domain_separator, prf_inputs <: (u8 & t_Array (t_Array u8 (sz 33)) v_K))
      (fun temp_0_ i ->
          let domain_separator, prf_inputs:(u8 & t_Array (t_Array u8 (sz 33)) v_K) = temp_0_ in
          let i:usize = i in
          let prf_inputs:t_Array (t_Array u8 (sz 33)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize prf_inputs
              i
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (prf_inputs.[ i ]
                    <:
                    t_Array u8 (sz 33))
                  (sz 32)
                  domain_separator
                <:
                t_Array u8 (sz 33))
          in
          let domain_separator:u8 = domain_separator +! 1uy in
          domain_separator, prf_inputs <: (u8 & t_Array (t_Array u8 (sz 33)) v_K))
  in
  let (prf_outputs: t_Array (t_Array u8 v_ETA_RANDOMNESS_SIZE) v_K):t_Array
    (t_Array u8 v_ETA_RANDOMNESS_SIZE) v_K =
    Libcrux_ml_kem.Hash_functions.f_PRFxN #v_Hasher
      #v_K
      #FStar.Tactics.Typeclasses.solve
      v_ETA_RANDOMNESS_SIZE
      prf_inputs
  in
  let re_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_K
      (fun re_as_ntt temp_1_ ->
          let re_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            re_as_ntt
          in
          let _:usize = temp_1_ in
          true)
      re_as_ntt
      (fun re_as_ntt i ->
          let re_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            re_as_ntt
          in
          let i:usize = i in
          let re_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re_as_ntt
              i
              (Libcrux_ml_kem.Sampling.sample_from_binomial_distribution v_ETA
                  #v_Vector
                  (prf_outputs.[ i ] <: t_Slice u8)
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          let re_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re_as_ntt
              i
              (Libcrux_ml_kem.Ntt.ntt_binomially_sampled_ring_element #v_Vector
                  (re_as_ntt.[ i ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          re_as_ntt)
  in
  let result:(t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K & u8) =
    re_as_ntt, domain_separator
    <:
    (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K & u8)
  in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

let compress_then_serialize_u
      (v_K v_OUT_LEN v_COMPRESSION_FACTOR v_BLOCK_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (input: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (out: t_Slice u8)
     =
  let _:Prims.unit =
    assert ((v Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT * v v_COMPRESSION_FACTOR) / 8 ==
        320 \/
        (v Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT * v v_COMPRESSION_FACTOR) / 8 ==
        352)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Folds.fold_enumerated_slice input
      (fun out i ->
          let out:t_Slice u8 = out in
          let i:usize = i in
          (Core.Slice.impl__len #u8 out <: usize) =. v_OUT_LEN <: bool)
      out
      (fun out temp_1_ ->
          let out:t_Slice u8 = out in
          let i, re:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            temp_1_
          in
          let out:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
              ({
                  Core.Ops.Range.f_start = i *! (v_OUT_LEN /! v_K <: usize) <: usize;
                  Core.Ops.Range.f_end
                  =
                  (i +! sz 1 <: usize) *! (v_OUT_LEN /! v_K <: usize) <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  (out.[ {
                        Core.Ops.Range.f_start = i *! (v_OUT_LEN /! v_K <: usize) <: usize;
                        Core.Ops.Range.f_end
                        =
                        (i +! sz 1 <: usize) *! (v_OUT_LEN /! v_K <: usize) <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Libcrux_ml_kem.Serialize.compress_then_serialize_ring_element_u v_COMPRESSION_FACTOR
                      v_BLOCK_LEN
                      #v_Vector
                      re
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          out)
  in
  let result:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = admit () (* Panic freedom *) in
  let hax_temp_output:Prims.unit = result in
  out

let deserialize_then_decompress_u
      (v_K v_CIPHERTEXT_SIZE v_U_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
     =
  let u_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core.Array.from_fn #(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
      (fun temp_0_ ->
          let _:usize = temp_0_ in
          Libcrux_ml_kem.Polynomial.impl_1__ZERO #v_Vector ()
          <:
          Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let u_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice ((Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *!
          v_U_COMPRESSION_FACTOR
          <:
          usize) /!
        sz 8
        <:
        usize)
      (ciphertext <: t_Slice u8)
      (fun u_as_ntt temp_1_ ->
          let u_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            u_as_ntt
          in
          let _:usize = temp_1_ in
          true)
      u_as_ntt
      (fun u_as_ntt temp_1_ ->
          let u_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            u_as_ntt
          in
          let i, u_bytes:(usize & t_Slice u8) = temp_1_ in
          let u_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize u_as_ntt
              i
              (Libcrux_ml_kem.Serialize.deserialize_then_decompress_ring_element_u v_U_COMPRESSION_FACTOR
                  #v_Vector
                  u_bytes
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          let u_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize u_as_ntt
              i
              (Libcrux_ml_kem.Ntt.ntt_vector_u v_U_COMPRESSION_FACTOR
                  #v_Vector
                  (u_as_ntt.[ i ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          u_as_ntt)
  in
  let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K = u_as_ntt in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

let deserialize_secret_key
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (secret_key: t_Slice u8)
     =
  let secret_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core.Array.from_fn #(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
      (fun temp_0_ ->
          let _:usize = temp_0_ in
          Libcrux_ml_kem.Polynomial.impl_1__ZERO #v_Vector ()
          <:
          Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let secret_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT
      secret_key
      (fun secret_as_ntt temp_1_ ->
          let secret_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K
          =
            secret_as_ntt
          in
          let _:usize = temp_1_ in
          true)
      secret_as_ntt
      (fun secret_as_ntt temp_1_ ->
          let secret_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K
          =
            secret_as_ntt
          in
          let i, secret_bytes:(usize & t_Slice u8) = temp_1_ in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize secret_as_ntt
            i
            (Libcrux_ml_kem.Serialize.deserialize_to_uncompressed_ring_element #v_Vector
                secret_bytes
              <:
              Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          <:
          t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
  in
  let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    secret_as_ntt
  in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

let serialize_secret_key
      (v_K v_OUT_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (key: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
     =
  let out:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let out:t_Array u8 v_OUT_LEN =
    Rust_primitives.Hax.Folds.fold_enumerated_slice key
      (fun out temp_1_ ->
          let out:t_Array u8 v_OUT_LEN = out in
          let _:usize = temp_1_ in
          true)
      out
      (fun out temp_1_ ->
          let out:t_Array u8 v_OUT_LEN = out in
          let i, re:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            temp_1_
          in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
            ({
                Core.Ops.Range.f_start
                =
                i *! Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <: usize;
                Core.Ops.Range.f_end
                =
                (i +! sz 1 <: usize) *! Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <: usize
              }
              <:
              Core.Ops.Range.t_Range usize)
            (Core.Slice.impl__copy_from_slice #u8
                (out.[ {
                      Core.Ops.Range.f_start
                      =
                      i *! Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <: usize;
                      Core.Ops.Range.f_end
                      =
                      (i +! sz 1 <: usize) *! Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT
                      <:
                      usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
                (Libcrux_ml_kem.Serialize.serialize_uncompressed_ring_element #v_Vector re
                  <:
                  t_Slice u8)
              <:
              t_Slice u8)
          <:
          t_Array u8 v_OUT_LEN)
  in
  let result:t_Array u8 v_OUT_LEN = out in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

let serialize_public_key
      (v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (tt_as_ntt: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (seed_for_a: t_Slice u8)
     =
  let public_key_serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    Rust_primitives.Hax.repeat 0uy v_PUBLIC_KEY_SIZE
  in
  let public_key_serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range public_key_serialized
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_RANKED_BYTES_PER_RING_ELEMENT }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (public_key_serialized.[ {
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = v_RANKED_BYTES_PER_RING_ELEMENT
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (serialize_secret_key v_K v_RANKED_BYTES_PER_RING_ELEMENT #v_Vector tt_as_ntt
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let public_key_serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from public_key_serialized
      ({ Core.Ops.Range.f_start = v_RANKED_BYTES_PER_RING_ELEMENT }
        <:
        Core.Ops.Range.t_RangeFrom usize)
      (Core.Slice.impl__copy_from_slice #u8
          (public_key_serialized.[ { Core.Ops.Range.f_start = v_RANKED_BYTES_PER_RING_ELEMENT }
              <:
              Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          seed_for_a
        <:
        t_Slice u8)
  in
  let result:t_Array u8 v_PUBLIC_KEY_SIZE = public_key_serialized in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

#push-options "--admit_smt_queries true"

let decrypt_unpacked
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR:
          usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (secret_key: Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
     =
  let u_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    deserialize_then_decompress_u v_K v_CIPHERTEXT_SIZE v_U_COMPRESSION_FACTOR #v_Vector ciphertext
  in
  let v:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Serialize.deserialize_then_decompress_ring_element_v v_V_COMPRESSION_FACTOR
      #v_Vector
      (ciphertext.[ { Core.Ops.Range.f_start = v_VECTOR_U_ENCODED_SIZE }
          <:
          Core.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
  in
  let message:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Matrix.compute_message v_K
      #v_Vector
      v
      secret_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt
      u_as_ntt
  in
  Libcrux_ml_kem.Serialize.compress_then_serialize_message #v_Vector message

#pop-options

let decrypt
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR:
          usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (secret_key: t_Slice u8)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
     =
  let secret_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    deserialize_secret_key v_K #v_Vector secret_key
  in
  let secret_key_unpacked:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector =
    { Libcrux_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt = secret_as_ntt }
    <:
    Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector
  in
  let result:t_Array u8 (sz 32) =
    decrypt_unpacked v_K
      v_CIPHERTEXT_SIZE
      v_VECTOR_U_ENCODED_SIZE
      v_U_COMPRESSION_FACTOR
      v_V_COMPRESSION_FACTOR
      #v_Vector
      secret_key_unpacked
      ciphertext
  in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

#push-options "--admit_smt_queries true"

let encrypt_unpacked
      (v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_LEN v_C2_LEN v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR v_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (public_key: Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector)
      (message: t_Array u8 (sz 32))
      (randomness: t_Slice u8)
     =
  let (prf_input: t_Array u8 (sz 33)):t_Array u8 (sz 33) =
    Libcrux_ml_kem.Utils.into_padded_array (sz 33) randomness
  in
  let r_as_ntt, domain_separator:(t_Array
      (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K &
    u8) =
    sample_vector_cbd_then_ntt v_K v_ETA1 v_ETA1_RANDOMNESS_SIZE #v_Vector #v_Hasher prf_input 0uy
  in
  let error_1_, domain_separator:(t_Array
      (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K &
    u8) =
    sample_ring_element_cbd v_K
      v_ETA2_RANDOMNESS_SIZE
      v_ETA2
      #v_Vector
      #v_Hasher
      prf_input
      domain_separator
  in
  let prf_input:t_Array u8 (sz 33) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize prf_input (sz 32) domain_separator
  in
  let (prf_output: t_Array u8 v_ETA2_RANDOMNESS_SIZE):t_Array u8 v_ETA2_RANDOMNESS_SIZE =
    Libcrux_ml_kem.Hash_functions.f_PRF #v_Hasher
      #v_K
      #FStar.Tactics.Typeclasses.solve
      v_ETA2_RANDOMNESS_SIZE
      (prf_input <: t_Slice u8)
  in
  let error_2_:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Sampling.sample_from_binomial_distribution v_ETA2
      #v_Vector
      (prf_output <: t_Slice u8)
  in
  let u:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Libcrux_ml_kem.Matrix.compute_vector_u v_K
      #v_Vector
      public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_A
      r_as_ntt
      error_1_
  in
  let message_as_ring_element:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Serialize.deserialize_then_decompress_message #v_Vector message
  in
  let v:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Matrix.compute_ring_element_v v_K
      #v_Vector
      public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt
      r_as_ntt
      error_2_
      message_as_ring_element
  in
  let ciphertext:t_Array u8 v_CIPHERTEXT_SIZE = Rust_primitives.Hax.repeat 0uy v_CIPHERTEXT_SIZE in
  let ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range ciphertext
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_C1_LEN }
        <:
        Core.Ops.Range.t_Range usize)
      (compress_then_serialize_u v_K
          v_C1_LEN
          v_U_COMPRESSION_FACTOR
          v_BLOCK_LEN
          #v_Vector
          u
          (ciphertext.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_C1_LEN }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from ciphertext
      ({ Core.Ops.Range.f_start = v_C1_LEN } <: Core.Ops.Range.t_RangeFrom usize)
      (Libcrux_ml_kem.Serialize.compress_then_serialize_ring_element_v v_V_COMPRESSION_FACTOR
          v_C2_LEN
          #v_Vector
          v
          (ciphertext.[ { Core.Ops.Range.f_start = v_C1_LEN } <: Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  ciphertext

#pop-options

let encrypt
      (v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_LEN v_C2_LEN v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR v_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (public_key: t_Slice u8)
      (message: t_Array u8 (sz 32))
      (randomness: t_Slice u8)
     =
  let tt_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Libcrux_ml_kem.Serialize.deserialize_ring_elements_reduced v_T_AS_NTT_ENCODED_SIZE
      v_K
      #v_Vector
      (public_key.[ { Core.Ops.Range.f_end = v_T_AS_NTT_ENCODED_SIZE }
          <:
          Core.Ops.Range.t_RangeTo usize ]
        <:
        t_Slice u8)
  in
  let seed:t_Slice u8 =
    public_key.[ { Core.Ops.Range.f_start = v_T_AS_NTT_ENCODED_SIZE }
      <:
      Core.Ops.Range.t_RangeFrom usize ]
  in
  let v_A:t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
    Libcrux_ml_kem.Matrix.sample_matrix_A v_K
      #v_Vector
      #v_Hasher
      (Libcrux_ml_kem.Utils.into_padded_array (sz 34) seed <: t_Array u8 (sz 34))
      false
  in
  let (seed_for_A: t_Array u8 (sz 32)):t_Array u8 (sz 32) =
    Core.Result.impl__unwrap #(t_Array u8 (sz 32))
      #Core.Array.t_TryFromSliceError
      (Core.Convert.f_try_into #(t_Slice u8)
          #(t_Array u8 (sz 32))
          #FStar.Tactics.Typeclasses.solve
          seed
        <:
        Core.Result.t_Result (t_Array u8 (sz 32)) Core.Array.t_TryFromSliceError)
  in
  let public_key_unpacked:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector =
    {
      Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt = tt_as_ntt;
      Libcrux_ml_kem.Ind_cpa.Unpacked.f_A = v_A;
      Libcrux_ml_kem.Ind_cpa.Unpacked.f_seed_for_A = seed_for_A
    }
    <:
    Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector
  in
  let result:t_Array u8 v_CIPHERTEXT_SIZE =
    encrypt_unpacked v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_LEN v_C2_LEN
      v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR v_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2
      v_ETA2_RANDOMNESS_SIZE #v_Vector #v_Hasher public_key_unpacked message randomness
  in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

let generate_keypair_unpacked
      (v_K v_ETA1 v_ETA1_RANDOMNESS_SIZE: usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (key_generation_seed: t_Slice u8)
     =
  let hashed:t_Array u8 (sz 64) =
    Libcrux_ml_kem.Hash_functions.f_G #v_Hasher
      #v_K
      #FStar.Tactics.Typeclasses.solve
      key_generation_seed
  in
  let seed_for_A, seed_for_secret_and_error:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8 (hashed <: t_Slice u8) (sz 32)
  in
  let v_A_transpose:t_Array
    (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
    Libcrux_ml_kem.Matrix.sample_matrix_A v_K
      #v_Vector
      #v_Hasher
      (Libcrux_ml_kem.Utils.into_padded_array (sz 34) seed_for_A <: t_Array u8 (sz 34))
      true
  in
  let (prf_input: t_Array u8 (sz 33)):t_Array u8 (sz 33) =
    Libcrux_ml_kem.Utils.into_padded_array (sz 33) seed_for_secret_and_error
  in
  let secret_as_ntt, domain_separator:(t_Array
      (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K &
    u8) =
    sample_vector_cbd_then_ntt v_K v_ETA1 v_ETA1_RANDOMNESS_SIZE #v_Vector #v_Hasher prf_input 0uy
  in
  let error_as_ntt, _:(t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K & u8
  ) =
    sample_vector_cbd_then_ntt v_K
      v_ETA1
      v_ETA1_RANDOMNESS_SIZE
      #v_Vector
      #v_Hasher
      prf_input
      domain_separator
  in
  let tt_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Libcrux_ml_kem.Matrix.compute_As_plus_e v_K #v_Vector v_A_transpose secret_as_ntt error_as_ntt
  in
  let (seed_for_A: t_Array u8 (sz 32)):t_Array u8 (sz 32) =
    Core.Result.impl__unwrap #(t_Array u8 (sz 32))
      #Core.Array.t_TryFromSliceError
      (Core.Convert.f_try_into #(t_Slice u8)
          #(t_Array u8 (sz 32))
          #FStar.Tactics.Typeclasses.solve
          seed_for_A
        <:
        Core.Result.t_Result (t_Array u8 (sz 32)) Core.Array.t_TryFromSliceError)
  in
  let pk:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector =
    {
      Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt = tt_as_ntt;
      Libcrux_ml_kem.Ind_cpa.Unpacked.f_A = v_A_transpose;
      Libcrux_ml_kem.Ind_cpa.Unpacked.f_seed_for_A = seed_for_A
    }
    <:
    Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector
  in
  let sk:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector =
    { Libcrux_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt = secret_as_ntt }
    <:
    Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector
  in
  let result:(Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector &
    Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector) =
    sk, pk
    <:
    (Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector &
      Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector)
  in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

let generate_keypair
      (v_K v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_RANKED_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (key_generation_seed: t_Slice u8)
     =
  let sk, pk:(Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector &
    Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector) =
    generate_keypair_unpacked v_K
      v_ETA1
      v_ETA1_RANDOMNESS_SIZE
      #v_Vector
      #v_Hasher
      key_generation_seed
  in
  let public_key_serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    serialize_public_key v_K
      v_RANKED_BYTES_PER_RING_ELEMENT
      v_PUBLIC_KEY_SIZE
      #v_Vector
      pk.Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt
      (pk.Libcrux_ml_kem.Ind_cpa.Unpacked.f_seed_for_A <: t_Slice u8)
  in
  let secret_key_serialized:t_Array u8 v_PRIVATE_KEY_SIZE =
    serialize_secret_key v_K
      v_PRIVATE_KEY_SIZE
      #v_Vector
      sk.Libcrux_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt
  in
  let result:(t_Array u8 v_PRIVATE_KEY_SIZE & t_Array u8 v_PUBLIC_KEY_SIZE) =
    secret_key_serialized, public_key_serialized
    <:
    (t_Array u8 v_PRIVATE_KEY_SIZE & t_Array u8 v_PUBLIC_KEY_SIZE)
  in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result
