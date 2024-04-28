module Libcrux_ml_kem.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val compress_then_serialize_10_
      (v_OUT_LEN: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

val compress_then_serialize_11_
      (v_OUT_LEN: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

val compress_then_serialize_4_
      (v_OUT_LEN: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

val compress_then_serialize_5_
      (v_OUT_LEN: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

val compress_then_serialize_message (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement)
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val compress_then_serialize_ring_element_u
      (v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

val compress_then_serialize_ring_element_v
      (v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

val deserialize_then_decompress_10_ (serialized: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_11_ (serialized: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_4_ (serialized: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_5_ (serialized: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_message (serialized: t_Array u8 (sz 32))
    : Prims.Pure Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_ring_element_u
      (v_COMPRESSION_FACTOR: usize)
      (serialized: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_ring_element_v
      (v_COMPRESSION_FACTOR: usize)
      (serialized: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Only use with public values.
/// This MUST NOT be used with secret inputs, like its caller `deserialize_ring_elements_reduced`.
val deserialize_to_reduced_ring_element (serialized: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

/// This function deserializes ring elements and reduces the result by the field
/// modulus.
/// This function MUST NOT be used on secret inputs.
val deserialize_ring_elements_reduced (v_PUBLIC_KEY_SIZE v_K: usize) (public_key: t_Slice u8)
    : Prims.Pure (t_Array Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_to_uncompressed_ring_element (serialized: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val serialize_uncompressed_ring_element (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement)
    : Prims.Pure (t_Array u8 (sz 384)) Prims.l_True (fun _ -> Prims.l_True)
