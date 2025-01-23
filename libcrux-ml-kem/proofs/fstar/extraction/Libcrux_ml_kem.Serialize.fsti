module Libcrux_ml_kem.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Traits in
  ()

[@@ "opaque_to_smt"]
let field_modulus_range (#v_Vector: Type0)
        {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
        (a: v_Vector) =
    let coef = Libcrux_ml_kem.Vector.Traits.f_to_i16_array a in
    forall (i:nat). i < 16 ==> v (Seq.index coef i) > -(v Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS) /\
        v (Seq.index coef i) < v Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS

[@@ "opaque_to_smt"]
let coefficients_field_modulus_range (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
    forall (i:nat). i < 16 ==> field_modulus_range (Seq.index re.f_coefficients i)

val to_unsigned_field_modulus
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (a: v_Vector)
    : Prims.Pure v_Vector
      (requires field_modulus_range a)
      (ensures
        fun result ->
          let result:v_Vector = result in
          forall (i: nat).
            i < 16 ==>
            v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array result) i) >= 0 /\
            v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array result) i) <
            v Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS)

val compress_then_serialize_message
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_Array u8 (sz 32))
      (requires coefficients_field_modulus_range re)
      (ensures
        fun result ->
          let result:t_Array u8 (sz 32) = result in
          result ==
          Spec.MLKEM.compress_then_encode_message (Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector
                re))

val deserialize_then_decompress_message
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Array u8 (sz 32))
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      Prims.l_True
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = result in
          Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector result ==
          Spec.MLKEM.decode_then_decompress_message serialized)

val serialize_uncompressed_ring_element
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_Array u8 (sz 384))
      (requires coefficients_field_modulus_range re)
      (ensures
        fun result ->
          let result:t_Array u8 (sz 384) = result in
          result ==
          Spec.MLKEM.byte_encode 12 (Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector re))

val deserialize_to_uncompressed_ring_element
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        (Core.Slice.impl__len #u8 serialized <: usize) =.
        Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT)
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = result in
          Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector result ==
          Spec.MLKEM.byte_decode 12 serialized)

/// Only use with public values.
/// This MUST NOT be used with secret inputs, like its caller `deserialize_ring_elements_reduced`.
val deserialize_to_reduced_ring_element
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        (Core.Slice.impl__len #u8 serialized <: usize) =.
        Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT)
      (fun _ -> Prims.l_True)

/// See [deserialize_ring_elements_reduced_out].
val deserialize_ring_elements_reduced
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (public_key: t_Slice u8)
      (deserialized_pk: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
    : Prims.Pure (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (requires
        Spec.MLKEM.is_rank v_K /\
        Seq.length public_key == v (Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE v_K))
      (ensures
        fun deserialized_pk_future ->
          let deserialized_pk_future:t_Array
            (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            deserialized_pk_future
          in
          Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K #v_Vector deserialized_pk_future ==
          Spec.MLKEM.vector_decode_12 #v_K public_key)

/// This function deserializes ring elements and reduces the result by the field
/// modulus.
/// This function MUST NOT be used on secret inputs.
val deserialize_ring_elements_reduced_out
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (public_key: t_Slice u8)
    : Prims.Pure (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (requires
        Spec.MLKEM.is_rank v_K /\
        Seq.length public_key == v (Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE v_K))
      (ensures
        fun result ->
          let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            result
          in
          forall (i: nat). i < v v_K ==> coefficients_field_modulus_range (Seq.index result i))

val compress_then_serialize_10_
      (v_OUT_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_Array u8 v_OUT_LEN)
      (requires v v_OUT_LEN == 320 /\ coefficients_field_modulus_range re)
      (fun _ -> Prims.l_True)

val compress_then_serialize_11_
      (v_OUT_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

val compress_then_serialize_ring_element_u
      (v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_Array u8 v_OUT_LEN)
      (requires
        (v v_COMPRESSION_FACTOR == 10 \/ v v_COMPRESSION_FACTOR == 11) /\
        v v_OUT_LEN == 32 * v v_COMPRESSION_FACTOR /\ coefficients_field_modulus_range re)
      (ensures
        fun result ->
          let result:t_Array u8 v_OUT_LEN = result in
          result ==
          Spec.MLKEM.compress_then_byte_encode (v v_COMPRESSION_FACTOR)
            (Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector re))

val compress_then_serialize_4_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires Seq.length serialized == 128 /\ coefficients_field_modulus_range re)
      (ensures
        fun serialized_future ->
          let serialized_future:t_Slice u8 = serialized_future in
          Core.Slice.impl__len #u8 serialized_future == Core.Slice.impl__len #u8 serialized)

val compress_then_serialize_5_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires (Core.Slice.impl__len #u8 serialized <: usize) =. sz 160)
      (ensures
        fun serialized_future ->
          let serialized_future:t_Slice u8 = serialized_future in
          Core.Slice.impl__len #u8 serialized_future == Core.Slice.impl__len #u8 serialized)

val compress_then_serialize_ring_element_v
      (v_K v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        Spec.MLKEM.is_rank v_K /\
        v_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR v_K /\
        Seq.length out == v v_OUT_LEN /\ v v_OUT_LEN == 32 * v v_COMPRESSION_FACTOR /\
        coefficients_field_modulus_range re)
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          Core.Slice.impl__len #u8 out_future == Core.Slice.impl__len #u8 out /\
          out_future ==
          Spec.MLKEM.compress_then_encode_v #v_K
            (Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector re))

val deserialize_then_decompress_10_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires (Core.Slice.impl__len #u8 serialized <: usize) =. sz 320)
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_11_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires (Core.Slice.impl__len #u8 serialized <: usize) =. sz 352)
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_ring_element_u
      (v_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        (v_COMPRESSION_FACTOR =. sz 10 || v_COMPRESSION_FACTOR =. sz 11) &&
        (Core.Slice.impl__len #u8 serialized <: usize) =. (sz 32 *! v_COMPRESSION_FACTOR <: usize))
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = result in
          Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector result ==
          Spec.MLKEM.byte_decode_then_decompress (v v_COMPRESSION_FACTOR) serialized)

val deserialize_then_decompress_4_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires (Core.Slice.impl__len #u8 serialized <: usize) =. sz 128)
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_5_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires (Core.Slice.impl__len #u8 serialized <: usize) =. sz 160)
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_ring_element_v
      (v_K v_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        Spec.MLKEM.is_rank v_K /\
        v_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR v_K /\
        Seq.length serialized == 32 * v v_COMPRESSION_FACTOR)
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = result in
          Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector result ==
          Spec.MLKEM.decode_then_decompress_v #v_K serialized)
