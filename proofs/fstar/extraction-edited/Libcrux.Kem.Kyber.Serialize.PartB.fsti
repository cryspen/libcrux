module Libcrux.Kem.Kyber.Serialize.PartB
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul
open MkSeq

val compress_then_serialize_10_
      (v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

val compress_then_serialize_11_
      (v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

val compress_then_serialize_4_
      (v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

val compress_then_serialize_5_
      (v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

val compress_then_serialize_message (re: Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
    : Pure (t_Array u8 (sz 32))
      (requires True)
      (ensures (fun res ->
        res == Spec.Kyber.compress_then_encode_message (Libcrux.Kem.Kyber.Arithmetic.to_spec_poly_b re)))

val compress_then_serialize_ring_element_u (#p:Spec.Kyber.params)
      (v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
    : Pure (t_Array u8 v_OUT_LEN)
      (requires (v_COMPRESSION_FACTOR = sz 10 || v_COMPRESSION_FACTOR = sz 11) /\
                v_OUT_LEN = Spec.Kyber.v_C1_BLOCK_SIZE p) 
      (ensures (fun _ -> True)) 
      
val compress_then_serialize_ring_element_v (#p:Spec.Kyber.params)
      (v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
    : Pure (t_Array u8 v_OUT_LEN)
      (requires (v_COMPRESSION_FACTOR = sz 4 || v_COMPRESSION_FACTOR = sz 5) /\
                 v_OUT_LEN = Spec.Kyber.v_C2_SIZE p)
      (ensures (fun res -> 
        res == 
        Spec.Kyber.compress_then_encode_v p 
          (Libcrux.Kem.Kyber.Arithmetic.to_spec_poly_b re)))

val deserialize_then_decompress_10_ (serialized: t_Slice u8)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_11_ (serialized: t_Slice u8)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_4_ (serialized: t_Slice u8)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_5_ (serialized: t_Slice u8)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_then_decompress_message (serialized: t_Array u8 (sz 32))
    : Pure (Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
      (requires True)
      (ensures fun res ->
        Libcrux.Kem.Kyber.Arithmetic.to_spec_poly_b res == 
        Spec.Kyber.decode_then_decompress_message serialized)

val deserialize_then_decompress_ring_element_u
      (v_COMPRESSION_FACTOR: usize)
      (serialized: t_Slice u8)
    : Pure (Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
      (requires v_COMPRESSION_FACTOR = sz 10 || v_COMPRESSION_FACTOR = sz 11)
      (ensures fun _ -> True)

val deserialize_then_decompress_ring_element_v (#p:Spec.Kyber.params)
      (v_COMPRESSION_FACTOR: usize)
      (serialized: t_Slice u8)
    : Pure (Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
      (requires (p.v_VECTOR_V_COMPRESSION_FACTOR == v_COMPRESSION_FACTOR /\
                 length serialized == Spec.Kyber.v_C2_SIZE p))
      (ensures fun res ->
       Libcrux.Kem.Kyber.Arithmetic.to_spec_poly_b res ==
       Spec.Kyber.decode_then_decompress_v p serialized)


val deserialize_to_uncompressed_ring_element (serialized: t_Slice u8)
    : Pure (Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
      (requires (length serialized == Spec.Kyber.v_BYTES_PER_RING_ELEMENT))
      (ensures fun _ -> True)

val serialize_uncompressed_ring_element (re: Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
    : Pure (t_Array u8 (sz 384))
      (requires True)
      (ensures (fun res -> True))
