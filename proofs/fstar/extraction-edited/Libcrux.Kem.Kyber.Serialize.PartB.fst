module Libcrux.Kem.Kyber.Serialize.PartB
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul
open MkSeq
open Libcrux.Kem.Kyber.Serialize.PartA

let cast_bound_lemma 
  #t #u
  (n: int_t t) 
  (d: bit_num t)
  : Lemma (requires bounded n d /\ d <= bits u /\ unsigned u /\ v n >= 0)
          (ensures  bounded (cast #(int_t t) #(int_t u) n) d)
          [SMTPat (bounded n d); SMTPat (cast #(int_t t) #(int_t u) n)]
  = ()

#push-options "--z3rlimit 60"
let int_t_d_cast_lemma #t #u d (n: int_t_d t d)
  : Lemma (requires bits t < bits u /\ v n >= 0)
          (ensures bounded (cast #(int_t t) #(int_t u) n) d)
          [SMTPat (bounded (cast #(int_t t) #(int_t u) n) d)]
  = Math.Lemmas.pow2_double_mult (bits u - 1);
    Math.Lemmas.small_mod (v n) (modulus u)
let mul_in_range (n m: nat)
  : Lemma
    (requires n <= 256 /\ m <= 256)
    (ensures range (n * m) usize_inttype)
  = Math.Lemmas.pow2_plus 8 8;
    Math.Lemmas.pow2_le_compat 32 16
#pop-options

#push-options "--fuel 0 --ifuel 1 --query_stats --z3rlimit 100"
let compress_then_serialize_10_
      v_OUT_LEN
      re
    =
  let accT = t_Array u8 v_OUT_LEN in
  let inv = fun (acc: t_Array u8 v_OUT_LEN) (i: usize) -> 
    // (forall (j: nat). j < 5 * v i ==> Seq.index accT j == Seq.index serialized j)
    // let coefs: t_Array i32 (sz 256) = map (fun (x: i32 {is_fe53 (v x)}) ->
    //        Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 10uy
    //          (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative x)
    //      ) re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
    // in
    // forall (j: usize). v j < v i * 40 + 40 ==>
    //   (
    //      assert (v j < v (sz 256) * v (sz 10));
    //      assert (v j < v v_OUT_LEN * v (sz 8));
         
    //      // offset_lemma (v i) (v v_OUT_LEN) 8 (v j);
    //      // offset_lemma (v i) 256 10 (v j);
    //      True
    //   //    get_bit_arr coefs (sz 10) j
    //   // == get_bit_arr acc   (sz  8) j
    //   )
    True
  in
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:t_Array u8 v_OUT_LEN =
    Rust_primitives.Iterators.foldi_chunks_exact #_ #accT #inv
      (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients)
      (sz 4)
      (serialized)
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUT_LEN = serialized in
          let i, coefficients:(usize & _) = temp_1_ in
          let coefficient1:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 10uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 0 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient2:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 10uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 1 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient3:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 10uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 2 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient4:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 10uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 3 ] <: i32
                  )
                <:
                u16)
          in
          let coef1, coef2, coef3, coef4, coef5:(u8 & u8 & u8 & u8 & u8) =
            compress_coefficients_10_ coefficient1 coefficient2 coefficient3 coefficient4
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (sz 5 *! i <: usize)
              coef1
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 1 <: usize)
              coef2
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 2 <: usize)
              coef3
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 3 <: usize)
              coef4
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 4 <: usize)
              coef5
          in
          serialized)
  in
  serialized
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"
let update5
  #n
  (s: t_Array 't n)
  (offset: usize {v offset + 5 <= v n})
  (i0 i1 i2 i3 i4: 't)
  : s': t_Array 't n {
     Seq.index s' (v offset +  0) == i0  /\
     Seq.index s' (v offset +  1) == i1  /\
     Seq.index s' (v offset +  2) == i2  /\
     Seq.index s' (v offset +  3) == i3  /\
     Seq.index s' (v offset +  4) == i4  /\
     (forall i. (i < v offset \/ i >= v offset + 5) ==> Seq.index s' i == Seq.index s i)
    }
 = let open Rust_primitives.Hax.Monomorphized_update_at in
    let s = update_at_usize s  offset          i0 in
    let s = update_at_usize s (offset +! sz  1) i1  in
    let s = update_at_usize s (offset +! sz  2) i2  in
    let s = update_at_usize s (offset +! sz  3) i3  in
    let s = update_at_usize s (offset +! sz  4) i4  in
    s
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100 --query_stats --split_queries no"
let compress_then_serialize_11_
      v_OUT_LEN re
  =
  let inv = fun (acc: t_Array u8 v_OUT_LEN) (i: usize) -> True in
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:t_Array u8 v_OUT_LEN =
    Rust_primitives.Iterators.foldi_chunks_exact #_ #_ #inv
      (Rust_primitives.unsize re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients)
      (sz 8)
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUT_LEN = serialized in
          let i, coefficients:(usize & t_Array Libcrux.Kem.Kyber.Arithmetic.wfFieldElement (sz 8)) = temp_1_ in
          let coefficient1 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 0 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient2 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 1 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient3 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 2 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient4 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 3 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient5 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 4 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient6 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 5 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient7 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 6 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient8 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 7 ] <: i32
                  )
                <:
                u16)
          in
          let coef1, coef2, coef3, coef4, coef5, coef6, coef7, coef8, coef9, coef10, coef11:(u8 & u8 &
            u8 &
            u8 &
            u8 &
            u8 &
            u8 &
            u8 &
            u8 &
            u8 &
            u8) =
            compress_coefficients_11_ coefficient1
              coefficient2
              coefficient3
              coefficient4
              coefficient5
              coefficient6
              coefficient7
              coefficient8
          in
          assert_spinoff (v i < 32 ==> 11 * v i + 11 <= 32 * 11);
          assert_spinoff (v i < 32 ==> range (v (sz 11) * v i) usize_inttype);
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (sz 11 *! i <: usize)
              coef1
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 1 <: usize)
              coef2
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 2 <: usize)
              coef3
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 3 <: usize)
              coef4
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 4 <: usize)
              coef5
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 5 <: usize)
              coef6
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 6 <: usize)
              coef7
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 7 <: usize)
              coef8
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 8 <: usize)
              coef9
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 9 <: usize)
              coef10
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 11 *! i <: usize) +! sz 10 <: usize)
              coef11
          in
          serialized)
  in
  serialized
#pop-options

let compress_then_serialize_4_ v_OUT_LEN re =
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let accT = t_Array u8 v_OUT_LEN in
  let inv (acc: accT) (i: usize) = True in
  let serialized:t_Array u8 v_OUT_LEN =
    Rust_primitives.Iterators.foldi_chunks_exact #_ #_ #inv
      (Rust_primitives.unsize re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients)
      (sz 2)
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUT_LEN = serialized in
          let i, coefficients:(usize & t_Array Libcrux.Kem.Kyber.Arithmetic.wfFieldElement (sz 2)) = temp_1_ in
          let coefficient1:u8 =
            cast (Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 4uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 0 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32)
            <:
            u8
          in
          let coefficient2:u8 =
            cast (Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 4uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 1 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32)
            <:
            u8
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              i
              ((coefficient2 <<! 4l <: u8) |. coefficient1 <: u8)
          in
          serialized)
  in
  serialized

let compress_then_serialize_5_
      v_OUT_LEN
      re
  =
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let accT = t_Array u8 v_OUT_LEN in
  let inv (acc: accT) (i: usize) = True in
  let serialized:t_Array u8 v_OUT_LEN =
    Rust_primitives.Iterators.foldi_chunks_exact #_ #_ #inv
      (Rust_primitives.unsize re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients)
      (sz 8)
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUT_LEN = serialized in
          let i, coefficients:(usize & t_Array Libcrux.Kem.Kyber.Arithmetic.wfFieldElement (sz 8)) = temp_1_ in
          let coefficient1:u8 =
            cast (Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 5uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 0 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32)
            <:
            u8
          in
          let coefficient2:u8 =
            cast (Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 5uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 1 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32)
            <:
            u8
          in
          let coefficient3:u8 =
            cast (Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 5uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 2 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32)
            <:
            u8
          in
          let coefficient4:u8 =
            cast (Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 5uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 3 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32)
            <:
            u8
          in
          let coefficient5:u8 =
            cast (Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 5uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 4 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32)
            <:
            u8
          in
          let coefficient6:u8 =
            cast (Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 5uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 5 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32)
            <:
            u8
          in
          let coefficient7:u8 =
            cast (Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 5uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 6 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32)
            <:
            u8
          in
          let coefficient8' = Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 5uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 7 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32 in
          let coefficient8:u8 =
            cast (Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 5uy
                  (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 7 ]
                        <:
                        i32)
                    <:
                    u16)
                <:
                i32)
            <:
            u8
          in
          let coef1, coef2, coef3, coef4, coef5:(u8 & u8 & u8 & u8 & u8) =
            compress_coefficients_5_ coefficient2
              coefficient1
              coefficient4
              coefficient3
              coefficient5
              coefficient7
              coefficient6
              coefficient8
          in
          assert_spinoff (v i < 32 ==> 5 * v i + 5 <= 32 * 5);
          assert_spinoff (v i < 32 ==> range (v (sz 5) * v i) usize_inttype);
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (sz 5 *! i <: usize)
              coef1
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 1 <: usize)
              coef2
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 2 <: usize)
              coef3
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 3 <: usize)
              coef4
          in
          let serialized:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 4 <: usize)
              coef5
          in
          serialized)
  in
  serialized

let compress_then_serialize_message re =
  let serialized:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let accT = t_Array u8 (sz 32) in
  let inv (acc: accT) (i: usize) = True in
  let serialized:t_Array u8 (sz 32) =
    Rust_primitives.Iterators.foldi_chunks_exact #_ #_ #inv
      (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients)
      (sz 8)
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 (sz 32) = serialized in
          let i, coefficients:(usize & t_Array Libcrux.Kem.Kyber.Arithmetic.wfFieldElement _) = temp_1_ in
          Rust_primitives.Iterators.foldi_slice #_ #_ #(fun _ _ -> True) 
            coefficients
            serialized
            (fun serialized temp_1_ ->
                let serialized:t_Array u8 (sz 32) = serialized in
                let j, coefficient:(usize & Libcrux.Kem.Kyber.Arithmetic.wfFieldElement) = temp_1_ in
                let coefficient:u16 =
                  Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative coefficient
                in
                let coefficient_compressed:u8 =
                  Libcrux.Kem.Kyber.Compress.compress_message_coefficient coefficient
                in
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
                  i
                  ((serialized.[ i ] <: u8) |. (coefficient_compressed <<! j <: u8) <: u8))
          <:
          t_Array u8 (sz 32))
  in
  admit (); // P-F 
  serialized

let compress_then_serialize_ring_element_u #p
      v_COMPRESSION_FACTOR
      v_OUT_LEN
      (re: Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement) =
  let _:Prims.unit = () <: Prims.unit in
  assert (
    (v (cast (v_COMPRESSION_FACTOR <: usize) <: u32) == 11) \/
    (v (cast (v_COMPRESSION_FACTOR <: usize) <: u32) == 10)
  );
  Rust_primitives.Integers.mk_int_equiv_lemma #usize_inttype (v v_COMPRESSION_FACTOR);
  match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
  | 10ul -> compress_then_serialize_10_ v_OUT_LEN re
  | 11ul -> compress_then_serialize_11_ v_OUT_LEN re
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"
        <:
        Rust_primitives.Hax.t_Never)

let compress_then_serialize_ring_element_v #p v_COMPRESSION_FACTOR v_OUT_LEN re =
  let _:Prims.unit = () <: Prims.unit in
  Rust_primitives.Integers.mk_int_equiv_lemma #usize_inttype (v v_COMPRESSION_FACTOR);
  let res = 
  assert (
    (v (cast (v_COMPRESSION_FACTOR <: usize) <: u32) == 4) \/
    (v (cast (v_COMPRESSION_FACTOR <: usize) <: u32) == 5)
  );
  match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
  | 4ul -> compress_then_serialize_4_ v_OUT_LEN re
  | 5ul -> compress_then_serialize_5_ v_OUT_LEN re
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)
  in
  admit (); // P-F
  res

#push-options "--z3rlimit 160"
let deserialize_then_decompress_10_ serialized =
  let _:Prims.unit = () <: Prims.unit in
  let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.cast_poly_b Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let accT = Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement in
  let inv (acc: accT) (i: usize) = True in
  let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
    Rust_primitives.Iterators.foldi_chunks_exact #_ #_ #inv
      serialized
      (sz 5)
      re
      (fun re temp_1_ ->
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement = re in
          let i, bytes:(usize & t_Array u8 (sz 5)) = temp_1_ in
          let byte1: int_t_d i32_inttype 8 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
          let byte2: int_t_d i32_inttype 8 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
          let byte3: int_t_d i32_inttype 8 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
          let byte4: int_t_d i32_inttype 8 = cast (bytes.[ sz 3 ] <: u8) <: i32 in
          let byte5: int_t_d i32_inttype 8 = cast (bytes.[ sz 4 ] <: u8) <: i32 in
          let coefficient1, coefficient2, coefficient3, coefficient4 =
            decompress_coefficients_10_ byte2 byte1 byte3 byte4 byte5
          in
          let coefficient1 = (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 10uy coefficient1
                           <:
                           i32) in
          let coefficient2 = (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 10uy coefficient2
                           <:
                           i32) in
          let coefficient3 = (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 10uy coefficient3
                           <:
                           i32) in
          let coefficient4 = (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 10uy coefficient4
                           <:
                           i32) in
          assert_spinoff (v i < 64 ==> 4 * v i + 4 <= 256);
          assert_spinoff (v i < 64 ==> range (v (sz 4) * v i) usize_inttype);
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 4 *! i <: usize)
                coefficient1 
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 4 *! i <: usize) +! sz 1 <: usize)
                coefficient2 
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 4 *! i <: usize) +! sz 2 <: usize)
                coefficient3
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 4 *! i <: usize) +! sz 3 <: usize)
                coefficient4
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          re)
  in
  re
#pop-options

#push-options "--z3rlimit 100 --ifuel 0"
let deserialize_then_decompress_11_ serialized
    : Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
  let _:Prims.unit = () <: Prims.unit in
  let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.cast_poly_b Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
    Rust_primitives.Iterators.foldi_chunks_exact #_ #_ #(fun _ _ -> True)
      serialized
      (sz 11)
      re
      (fun re temp_1_ ->
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement = re in
          let i, bytes:(usize & t_Array u8 (sz 11)) = temp_1_ in
          assert (v i < 32);
          let byte1: int_t_d i32_inttype 8 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
          let byte2: int_t_d i32_inttype 8 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
          let byte3: int_t_d i32_inttype 8 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
          let byte4: int_t_d i32_inttype 8 = cast (bytes.[ sz 3 ] <: u8) <: i32 in
          let byte5: int_t_d i32_inttype 8 = cast (bytes.[ sz 4 ] <: u8) <: i32 in
          let byte6: int_t_d i32_inttype 8 = cast (bytes.[ sz 5 ] <: u8) <: i32 in
          let byte7: int_t_d i32_inttype 8 = cast (bytes.[ sz 6 ] <: u8) <: i32 in
          let byte8: int_t_d i32_inttype 8 = cast (bytes.[ sz 7 ] <: u8) <: i32 in
          let byte9: int_t_d i32_inttype 8 = cast (bytes.[ sz 8 ] <: u8) <: i32 in
          let byte10: int_t_d i32_inttype 8 = cast (bytes.[ sz 9 ] <: u8) <: i32 in
          let byte11: int_t_d i32_inttype 8 = cast (bytes.[ sz 10 ] <: u8) <: i32 in
          let
          coefficient1,
          coefficient2,
          coefficient3,
          coefficient4,
          coefficient5,
          coefficient6,
          coefficient7,
          coefficient8 =
            decompress_coefficients_11_ byte2 byte1 byte3 byte5 byte4 byte6 byte7 byte9 byte8 byte10
              byte11
          in
          let coefficient1 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient1 in
          let coefficient2 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient2 in
          let coefficient3 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient3 in
          let coefficient4 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient4 in
          let coefficient5 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient5 in
          let coefficient6 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient6 in
          let coefficient7 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient7 in
          let coefficient8 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient8 in
          assert_spinoff (8 * v i + 8 <= 256);
          assert_spinoff (range (v (sz 8) * v i) usize_inttype);
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 8 *! i <: usize)
                coefficient1
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 1 <: usize)
                coefficient2
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 2 <: usize)
                coefficient3
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 3 <: usize)
                coefficient4
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 4 <: usize)
                coefficient5
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 5 <: usize)
                coefficient6
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 6 <: usize)
                coefficient7
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 7 <: usize)
                coefficient8
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          re)
  in
  re
#pop-options

#push-options "--z3rlimit 100"
let deserialize_then_decompress_4_ serialized =
  let _:Prims.unit = () <: Prims.unit in
  let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.cast_poly_b Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
    Rust_primitives.Iterators.foldi_slice #_ #_ #(fun _ _ -> True)
      serialized
      re
      (fun re temp_1_ ->
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement = re in
          let i, byte:(usize & u8) = temp_1_ in
          let coefficient1, coefficient2 = decompress_coefficients_4_ byte in
          assert_spinoff (v i < 128 ==> 2 * v i + 1 < 256);
          assert_spinoff (v i < 128 ==> range (v (sz 2) * v i) usize_inttype);
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 2 *! i <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 4uy coefficient1
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 2 *! i <: usize) +! sz 1 <: usize)
                (Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 4uy coefficient2
                  <:
                  i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          re)
  in
  re
#pop-options

#push-options "--z3rlimit 150"
let deserialize_then_decompress_5_ serialized =
  let _:Prims.unit = () <: Prims.unit in
  let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.cast_poly_b Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
     Rust_primitives.Iterators.foldi_chunks_exact #_ #_ #(fun _ _ -> True)
      serialized (sz 5)
      re
      (fun re temp_1_ ->
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement = re in
          let i, bytes:(usize & t_Array u8 (sz 5)) = temp_1_ in
          assert (v i < 32);
          let byte1 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
          let byte2 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
          let byte3 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
          let byte4 = cast (bytes.[ sz 3 ] <: u8) <: i32 in
          let byte5 = cast (bytes.[ sz 4 ] <: u8) <: i32 in
          let
          coefficient1,
          coefficient2,
          coefficient3,
          coefficient4,
          coefficient5,
          coefficient6,
          coefficient7,
          coefficient8 =
            decompress_coefficients_5_ byte1 byte2 byte3 byte4 byte5
          in
          let coefficient1 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient1 in
          let coefficient2 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient2 in
          let coefficient3 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient3 in
          let coefficient4 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient4 in
          let coefficient5 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient5 in
          let coefficient6 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient6 in
          let coefficient7 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient7 in
          let coefficient8 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient8 in
          // assert (Seq.length serialized == 160);
          // // assert_norm (160 / 5 == 32);
          // assert_spinoff (v i < Seq.length serialized);
          // assert (v i < 32);
          assert_spinoff (v i < 32 ==> 8 * v i + 8 <= 256);
          mul_in_range 8 (v i);
          assert_spinoff (v i < 32 ==> range (v (sz 8) * v i) usize_inttype);
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 8 *! i <: usize)
                coefficient1
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 1 <: usize)
                coefficient2
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 2 <: usize)
                coefficient3
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 3 <: usize)
                coefficient4
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 4 <: usize)
                coefficient5
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 5 <: usize)
                coefficient6
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 6 <: usize)
                coefficient7
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 8 *! i <: usize) +! sz 7 <: usize)
                coefficient8
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          re)
  in
  re
#pop-options

#push-options "--z3rlimit 60"
let deserialize_then_decompress_message (serialized: t_Array u8 (sz 32)) =
  let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
   Libcrux.Kem.Kyber.Arithmetic.cast_poly_b Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
    Rust_primitives.Iterators.foldi_slice #_ #_ #(fun _ _ -> True)
      serialized
      re
      (fun re temp_1_ ->
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement = re in
          let i, byte:(usize & u8) = temp_1_ in
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                    Core.Ops.Range.f_start = sz 0;
                    Core.Ops.Range.f_end = sz 8
                  }
                  <:
                  Core.Ops.Range.t_Range usize)
              <:
              Core.Ops.Range.t_Range usize)
            re
            (fun re j ->
                let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement = re in
                let j:usize = j in
                let coefficient_compressed:i32 = cast ((byte >>! j <: u8) &. 1uy <: u8) <: i32 in
                lemma_get_bit_bounded' coefficient_compressed 1;
                let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
                  {
                    re with
                    Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      ((sz 8 *! i <: usize) +! j <: usize)
                      (Libcrux.Kem.Kyber.Compress.decompress_message_coefficient coefficient_compressed

                        <:
                        i32)
                  }
                  <:
                  Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
                in
                re)
          <:
          Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
  in
  admit(); //P-F
  re
#pop-options

let deserialize_then_decompress_ring_element_u v_COMPRESSION_FACTOR serialized = 
  let _:Prims.unit = () <: Prims.unit in
  mk_int_equiv_lemma #usize_inttype (v v_COMPRESSION_FACTOR);
  assert (v (cast (v_COMPRESSION_FACTOR <: usize) <: u32) == 10 \/ v (cast (v_COMPRESSION_FACTOR <: usize) <: u32) == 11);
  match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
  | 10ul -> deserialize_then_decompress_10_ serialized
  | 11ul -> deserialize_then_decompress_11_ serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let deserialize_then_decompress_ring_element_v v_COMPRESSION_FACTOR serialized =
  let _:Prims.unit = () <: Prims.unit in
  mk_int_equiv_lemma #u32_inttype (v v_COMPRESSION_FACTOR);
  assert (v (cast (v_COMPRESSION_FACTOR <: usize) <: u32) == 4 \/ v (cast (v_COMPRESSION_FACTOR <: usize) <: u32) == 5);
  let res = 
  match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
  | 4ul -> deserialize_then_decompress_4_ serialized
  | 5ul -> deserialize_then_decompress_5_ serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)
  in
  admit(); //P-F
  res

#push-options "--z3rlimit 100"
let deserialize_to_uncompressed_ring_element (serialized: t_Slice u8) = 
  let _:Prims.unit = () <: Prims.unit in
  let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
   Libcrux.Kem.Kyber.Arithmetic.cast_poly_b Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
    Rust_primitives.Iterators.foldi_chunks_exact #_ #_ #(fun _ _ -> True)
      serialized
      (sz 3)
      re
      (fun re temp_1_ ->
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement = re in
          let i, bytes:(usize & t_Array u8 (sz 3)) = temp_1_ in
          let byte1:int_t_d i32_inttype 8 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
          let byte2:int_t_d i32_inttype 8 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
          let byte3:int_t_d i32_inttype 8 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
          let coef1 = (((byte2 &. 15l <: i32) <<! 8l <: i32) |. (byte1 &. 255l <: i32) <: i32) in
          let coef2 = ((byte3 <<! 4l <: i32) |. ((byte2 >>! 4l <: i32) &. 15l <: i32) <: i32) in
          lemma_get_bit_bounded' coef1 11;
          lemma_get_bit_bounded' coef2 11;
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 2 *! i <: usize)
                coef1
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 2 *! i <: usize) +! sz 1 <: usize)
                coef2
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
          in
          re)
  in
  re
#pop-options

#push-options "--z3rlimit 100"
let serialize_uncompressed_ring_element (re: Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement) =
  let serialized:t_Array u8 (sz 384) = Rust_primitives.Hax.repeat 0uy (sz 384) in
  let serialized:t_Array u8 (sz 384) =
    Rust_primitives.Iterators.foldi_chunks_exact #_ #_ #(fun _ _ -> True)
      (Rust_primitives.unsize re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients)
      (sz 2)
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 (sz 384) = serialized in
          let i, coefficients:(usize & t_Array (Libcrux.Kem.Kyber.Arithmetic.i32_b (v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS - 1)) (sz 2)) = temp_1_ in
          assert (v i < 128);
          let coefficient1:u16 =
            Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 0 ] <: i32)
          in
          let coefficient2:u16 =
            Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 1 ] <: i32)
          in
          let coef1, coef2, coef3:(u8 & u8 & u8) =
            compress_coefficients_3_ coefficient1 coefficient2
          in
          assert_spinoff (3 * v i + 3 <= 384);
          assert_spinoff (range (v (sz 3) * v i) usize_inttype);
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (sz 3 *! i <: usize)
              coef1
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 3 *! i <: usize) +! sz 1 <: usize)
              coef2
          in
          let serialized:t_Array u8 (sz 384) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 3 *! i <: usize) +! sz 2 <: usize)
              coef3
          in
          serialized)
  in
  serialized
#pop-options
