module Libcrux.Kem.Kyber.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul
open MkSeq

let int_arr_bitwise_eq
       #t1 #t2 #n1 #n2
       (arr1: t_Array (int_t t1) n1)
       (d1: bit_num t1)
       (arr2: t_Array (int_t t2) n2)
       (d2: bit_num t2 {v n1 * d1 == v n2 * d2})
     = forall i. i < v n1 * d1
       ==> bit_vec_of_int_arr arr1 d1 i == bit_vec_of_int_arr arr2 d2 i

val compress_coefficients_10_ (coefficient1 coefficient2 coefficient3 coefficient4: i32)
    : Prims.Pure (u8 & u8 & u8 & u8 & u8) 
      (requires True)
      (ensures fun tuple ->
         int_arr_bitwise_eq
                (create4 (coefficient1, coefficient2, coefficient3, coefficient4)) 10
                (create5 tuple) 8
      )

val compress_coefficients_11_
      (coefficient1 coefficient2 coefficient3 coefficient4 coefficient5 coefficient6 coefficient7 coefficient8:
          int_t_d i32_inttype 11)
    : Prims.Pure (u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8)
      (requires True)
      (ensures fun tuple ->
         int_arr_bitwise_eq
                (create8 (coefficient1, coefficient2, coefficient3, coefficient4, coefficient5, coefficient6, coefficient7, coefficient8)) 11
                (create11 tuple) 8
      )

val compress_coefficients_3_ (coefficient1 coefficient2: int_t_d u16_inttype 12)
    : Prims.Pure (u8 & u8 & u8)
    (requires True)
    (ensures fun tuple ->
       int_arr_bitwise_eq
              (create2 (coefficient1, coefficient2)) 12
              (create3 tuple) 8
    )

val compress_coefficients_5_
      (coefficient2 coefficient1 coefficient4 coefficient3 coefficient5 coefficient7 coefficient6 coefficient8: int_t_d u8_inttype 5)
    : Prims.Pure (u8 & u8 & u8 & u8 & u8)
      (requires True)
      (ensures fun tuple ->
         int_arr_bitwise_eq
                (create8 (coefficient1, coefficient2, coefficient3, coefficient4, coefficient5, coefficient6, coefficient7, coefficient8)) 5
                (create5 tuple) 8
      )

val decompress_coefficients_10_ (byte2 byte1 byte3 byte4 byte5: int_t_d i32_inttype 8)
    : Prims.Pure (i32 & i32 & i32 & i32)
      (requires True)
      (ensures fun tuple ->
         int_arr_bitwise_eq
                (create5 (byte1, byte2, byte3, byte4, byte5)) 8
                (create4 tuple) 10
      )

val decompress_coefficients_11_
      (byte2 byte1 byte3 byte5 byte4 byte6 byte7 byte9 byte8 byte10 byte11: int_t_d i32_inttype 8)
    : Prims.Pure (i32 & i32 & i32 & i32 & i32 & i32 & i32 & i32)
      (requires True)
      (ensures fun tuple ->
         int_arr_bitwise_eq
                (create11 (byte1, byte2, byte3, byte4, byte5, byte6, byte7, byte8, byte9, byte10, byte11)) 8
                (create8 tuple) 11
      )

val decompress_coefficients_4_ (byte: u8)
    : Prims.Pure (i32 & i32) 
      (requires True)
      (ensures fun tuple ->
         int_arr_bitwise_eq
                (create1 byte) 8
                (create2 tuple) 4
      )

val decompress_coefficients_5_ (byte1 byte2 byte3 byte4 byte5: int_t_d i32_inttype 5)
    : Prims.Pure (i32 & i32 & i32 & i32 & i32 & i32 & i32 & i32)
      (requires True)
      (ensures fun tuple ->
         int_arr_bitwise_eq
                (create5 (byte1, byte2, byte3, byte4, byte5)) 8
                (create8 tuple) 5
      )
      
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
    : Pure (t_Array u8 (sz 32))
      (requires True)
      (ensures (fun res ->
        res == Spec.Kyber.compress_then_encode_message (Libcrux.Kem.Kyber.Arithmetic.to_spec_poly re)))

val compress_then_serialize_ring_element_u (#p:Spec.Kyber.params)
      (v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Pure (t_Array u8 v_OUT_LEN)
      (requires (v_COMPRESSION_FACTOR = sz 10 || v_COMPRESSION_FACTOR = sz 11) /\
                v_OUT_LEN = Spec.Kyber.v_C1_BLOCK_SIZE p) 
      (ensures (fun _ -> True)) 
      
val compress_then_serialize_ring_element_v (#p:Spec.Kyber.params)
      (v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Pure (t_Array u8 v_OUT_LEN)
      (requires (v_COMPRESSION_FACTOR = sz 4 || v_COMPRESSION_FACTOR = sz 5) /\
                 v_OUT_LEN = Spec.Kyber.v_C2_SIZE p)
      (ensures (fun res -> 
        res == 
        Spec.Kyber.compress_then_encode_v p 
          (Libcrux.Kem.Kyber.Arithmetic.to_spec_poly re)))

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
    : Pure (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (requires True)
      (ensures fun res ->
        Libcrux.Kem.Kyber.Arithmetic.to_spec_poly res == 
        Spec.Kyber.decode_then_decompress_message serialized)

val deserialize_then_decompress_ring_element_u
      (v_COMPRESSION_FACTOR: usize)
      (serialized: t_Slice u8)
    : Pure (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (requires v_COMPRESSION_FACTOR = sz 10 || v_COMPRESSION_FACTOR = sz 11)
      (ensures fun _ -> True)

val deserialize_then_decompress_ring_element_v (#p:Spec.Kyber.params)
      (v_COMPRESSION_FACTOR: usize)
      (serialized: t_Slice u8)
    : Pure (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (requires (p.v_VECTOR_V_COMPRESSION_FACTOR == v_COMPRESSION_FACTOR /\
                 length serialized == Spec.Kyber.v_C2_SIZE p))
      (ensures fun res ->
       Libcrux.Kem.Kyber.Arithmetic.to_spec_poly res ==
       Spec.Kyber.decode_then_decompress_v p serialized)


val deserialize_to_uncompressed_ring_element (serialized: t_Slice u8)
    : Pure (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (requires (length serialized == Spec.Kyber.v_BYTES_PER_RING_ELEMENT))
      (ensures fun _ -> True)

val serialize_uncompressed_ring_element (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Pure (t_Array u8 (sz 384))
      (requires True)
      (ensures (fun res -> True))
