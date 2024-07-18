module Libcrux_ml_kem.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Traits in
  ()

val compress_then_serialize_10_
      (v_OUT_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_Array u8 v_OUT_LEN)
      (requires
        ((sz 20 *! (Libcrux_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT -! sz 1 <: usize) <: usize) +!
          sz 20
          <:
          usize) <=.
        v_OUT_LEN)
      (fun _ -> Prims.l_True)

val compress_then_serialize_11_
      (v_OUT_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_Array u8 v_OUT_LEN)
      (requires
        ((sz 22 *! (Libcrux_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT -! sz 1 <: usize) <: usize) +!
          sz 22
          <:
          usize) <=.
        v_OUT_LEN)
      (fun _ -> Prims.l_True)

val compress_then_serialize_4_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        ((sz 8 *! (Libcrux_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT -! sz 1 <: usize) <: usize) +!
          sz 8
          <:
          usize) <=.
        (Core.Slice.impl__len #u8 serialized <: usize))
      (fun _ -> Prims.l_True)

val compress_then_serialize_5_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        ((sz 10 *! (Libcrux_ml_kem.Polynomial.v_VECTORS_IN_RING_ELEMENT -! sz 1 <: usize) <: usize) +!
          sz 10
          <:
          usize) <=.
        (Core.Slice.impl__len #u8 serialized <: usize))
      (fun _ -> Prims.l_True)

val compress_then_serialize_message
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_Array u8 (sz 32))
      (requires (sz 32 +! sz 2 <: usize) <=. Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE)
      (fun _ -> Prims.l_True)

val compress_then_serialize_ring_element_u
      (v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_Array u8 v_OUT_LEN)
      (requires
        (v_COMPRESSION_FACTOR =. sz 10 || v_COMPRESSION_FACTOR =. sz 11) &&
        ((Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! v_COMPRESSION_FACTOR <: usize) /!
          sz 8
          <:
          usize) =.
        v_OUT_LEN)
      (fun _ -> Prims.l_True)

val compress_then_serialize_ring_element_v
      (v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (v_COMPRESSION_FACTOR =. sz 4 || v_COMPRESSION_FACTOR =. sz 5) &&
        ((Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! v_COMPRESSION_FACTOR <: usize) /!
          sz 8
          <:
          usize) =.
        v_OUT_LEN &&
        (Core.Slice.impl__len #u8 out <: usize) =. v_OUT_LEN)
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_10_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        (Core.Slice.impl__len #u8 serialized <: usize) =.
        ((Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! sz 10 <: usize) /! sz 8
          <:
          usize))
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_11_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        (Core.Slice.impl__len #u8 serialized <: usize) =.
        ((Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! sz 11 <: usize) /! sz 8
          <:
          usize))
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_4_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        (Core.Slice.impl__len #u8 serialized <: usize) =.
        ((Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! sz 4 <: usize) /! sz 8 <: usize
        ))
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_5_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        (Core.Slice.impl__len #u8 serialized <: usize) =.
        ((Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! sz 5 <: usize) /! sz 8 <: usize
        ))
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_message
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Array u8 (sz 32))
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_ring_element_u
      (v_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        (v_COMPRESSION_FACTOR =. sz 10 || v_COMPRESSION_FACTOR =. sz 11) &&
        (Core.Slice.impl__len #u8 serialized <: usize) =.
        ((Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! v_COMPRESSION_FACTOR <: usize) /!
          sz 8
          <:
          usize))
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_ring_element_v
      (v_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        (v_COMPRESSION_FACTOR =. sz 4 || v_COMPRESSION_FACTOR =. sz 5) &&
        (Core.Slice.impl__len #u8 serialized <: usize) =.
        ((Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! v_COMPRESSION_FACTOR <: usize) /!
          sz 8
          <:
          usize))
      (fun _ -> Prims.l_True)

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

/// This function deserializes ring elements and reduces the result by the field
/// modulus.
/// This function MUST NOT be used on secret inputs.
val deserialize_ring_elements_reduced
      (v_PUBLIC_KEY_SIZE v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (public_key: t_Slice u8)
    : Prims.Pure (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_to_uncompressed_ring_element
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (serialized: t_Slice u8)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        (Core.Slice.impl__len #u8 serialized <: usize) =.
        Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT)
      (fun _ -> Prims.l_True)

val serialize_uncompressed_ring_element
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_Array u8 (sz 384)) Prims.l_True (fun _ -> Prims.l_True)
