module Libcrux.Kem.Kyber.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul


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
