module Libcrux.Kem.Kyber.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val compress_coefficients_10_ (coefficient1 coefficient2 coefficient3 coefficient4: i32)
    : Prims.Pure (u8 & u8 & u8 & u8 & u8) Prims.l_True (fun _ -> Prims.l_True)

val compress_coefficients_11_
      (coefficient1 coefficient2 coefficient3 coefficient4 coefficient5 coefficient6 coefficient7 coefficient8:
          i32)
    : Prims.Pure (u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val compress_coefficients_3_ (coefficient1 coefficient2: u16)
    : Prims.Pure (u8 & u8 & u8) Prims.l_True (fun _ -> Prims.l_True)

val compress_coefficients_5_
      (coefficient2 coefficient1 coefficient4 coefficient3 coefficient5 coefficient7 coefficient6 coefficient8:
          u8)
    : Prims.Pure (u8 & u8 & u8 & u8 & u8) Prims.l_True (fun _ -> Prims.l_True)

val decompress_coefficients_10_ (byte2 byte1 byte3 byte4 byte5: i32)
    : Prims.Pure (i32 & i32 & i32 & i32) Prims.l_True (fun _ -> Prims.l_True)

val decompress_coefficients_11_
      (byte2 byte1 byte3 byte5 byte4 byte6 byte7 byte9 byte8 byte10 byte11: i32)
    : Prims.Pure (i32 & i32 & i32 & i32 & i32 & i32 & i32 & i32)
      Prims.l_True
      (fun _ -> Prims.l_True)

val decompress_coefficients_4_ (byte: u8)
    : Prims.Pure (i32 & i32) Prims.l_True (fun _ -> Prims.l_True)

val decompress_coefficients_5_ (byte1 byte2 byte3 byte4 byte5: i32)
    : Prims.Pure (i32 & i32 & i32 & i32 & i32 & i32 & i32 & i32)
      Prims.l_True
      (fun _ -> Prims.l_True)

val compress_then_serialize_10_
      (v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

val compress_then_serialize_11_
      (v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

val compress_then_serialize_4_
      (v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

val compress_then_serialize_5_
      (v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

val compress_then_serialize_message (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val compress_then_serialize_ring_element_u
      (v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

val compress_then_serialize_ring_element_v
      (v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

val deserialize_then_decompress_10_ (serialized: t_Slice u8)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_11_ (serialized: t_Slice u8)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_4_ (serialized: t_Slice u8)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_5_ (serialized: t_Slice u8)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_message (serialized: t_Array u8 (sz 32))
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_ring_element_u
      (v_COMPRESSION_FACTOR: usize)
      (serialized: t_Slice u8)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_ring_element_v
      (v_COMPRESSION_FACTOR: usize)
      (serialized: t_Slice u8)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Only use with public values.
/// This MUST NOT be used with secret inputs, like its caller `deserialize_ring_elements_reduced`.
val deserialize_to_reduced_ring_element (ring_element: t_Slice u8)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

/// This function deserializes ring elements and reduces the result by the field
/// modulus.
/// This function MUST NOT be used on secret inputs.
val deserialize_ring_elements_reduced (v_PUBLIC_KEY_SIZE v_K: usize) (public_key: t_Slice u8)
    : Prims.Pure (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_to_uncompressed_ring_element (serialized: t_Slice u8)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val serialize_uncompressed_ring_element (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Prims.Pure (t_Array u8 (sz 384)) Prims.l_True (fun _ -> Prims.l_True)
