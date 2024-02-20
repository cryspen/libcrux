module Libcrux.Kem.Kyber.Serialize
#set-options "--fuel 0 --ifuel 0 --z3rlimit 50 --retry 3"
open Core
open FStar.Mul

open Libcrux.Kem.Kyber.Arithmetic

open MkSeq
open BitVecEq

#push-options "--z3rlimit 480  --split_queries always"
[@@"opaque_to_smt"]
let compress_coefficients_10_ (coefficient1 coefficient2 coefficient3 coefficient4: i32) =
  let coef1:u8 = cast (coefficient1 &. 255l <: i32) <: u8 in
  let coef2:u8 =
    ((cast (coefficient2 &. 63l <: i32) <: u8) <<! 2l <: u8) |.
    (cast ((coefficient1 >>! 8l <: i32) &. 3l <: i32) <: u8)
  in
  let coef3:u8 =
    ((cast (coefficient3 &. 15l <: i32) <: u8) <<! 4l <: u8) |.
    (cast ((coefficient2 >>! 6l <: i32) &. 15l <: i32) <: u8)
  in
  let coef4:u8 =
    ((cast (coefficient4 &. 3l <: i32) <: u8) <<! 6l <: u8) |.
    (cast ((coefficient3 >>! 4l <: i32) &. 63l <: i32) <: u8)
  in
  let coef5:u8 = cast ((coefficient4 >>! 2l <: i32) &. 255l <: i32) <: u8 in
  bit_vec_equal_intro_principle ();
  coef1, coef2, coef3, coef4, coef5 <: (u8 & u8 & u8 & u8 & u8)
#pop-options

#push-options "--ifuel 1 --z3rlimit 600 --split_queries always"
[@@"opaque_to_smt"]
let compress_coefficients_11_
      coefficient1 coefficient2 coefficient3 coefficient4 coefficient5 coefficient6 coefficient7 coefficient8 =
  let coef1:u8 = cast (coefficient1 <: i32) <: u8 in
  let coef2:u8 =
    ((cast (coefficient2 &. 31l <: i32) <: u8) <<! 3l <: u8) |.
    (cast (coefficient1 >>! 8l <: i32) <: u8)
  in
  let coef3:u8 =
    ((cast (coefficient3 &. 3l <: i32) <: u8) <<! 6l <: u8) |.
    (cast (coefficient2 >>! 5l <: i32) <: u8)
  in
  let coef4:u8 = cast ((coefficient3 >>! 2l <: i32) &. 255l <: i32) <: u8 in
  let coef5:u8 =
    ((cast (coefficient4 &. 127l <: i32) <: u8) <<! 1l <: u8) |.
    (cast (coefficient3 >>! 10l <: i32) <: u8)
  in
  let coef6:u8 =
    ((cast (coefficient5 &. 15l <: i32) <: u8) <<! 4l <: u8) |.
    (cast (coefficient4 >>! 7l <: i32) <: u8)
  in
  let coef7:u8 =
    ((cast (coefficient6 &. 1l <: i32) <: u8) <<! 7l <: u8) |.
    (cast (coefficient5 >>! 4l <: i32) <: u8)
  in
  let coef8:u8 = cast ((coefficient6 >>! 1l <: i32) &. 255l <: i32) <: u8 in
  let coef9:u8 =
    ((cast (coefficient7 &. 63l <: i32) <: u8) <<! 2l <: u8) |.
    (cast (coefficient6 >>! 9l <: i32) <: u8)
  in
  let coef10:u8 =
    ((cast (coefficient8 &. 7l <: i32) <: u8) <<! 5l <: u8) |.
    (cast (coefficient7 >>! 6l <: i32) <: u8)
  in
  let coef11:u8 = cast (coefficient8 >>! 3l <: i32) <: u8 in
  bit_vec_equal_intro_principle ();
  coef1, coef2, coef3, coef4, coef5, coef6, coef7, coef8, coef9, coef10, coef11
  <:
  (u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8)
#pop-options

#push-options "--z3rlimit 20"
[@@"opaque_to_smt"]
let compress_coefficients_3_ coefficient1 coefficient2 =
  let coef1:u8 = cast (coefficient1 &. 255us <: u16) <: u8 in
  get_bit_pow2_minus_one_u16 255 (sz 0);
  let coef2:u8 =
    cast ((coefficient1 >>! 8l <: u16) |. ((coefficient2 &. 15us <: u16) <<! 4l <: u16) <: u16)
    <:
    u8
  in
  let coef3:u8 = cast ((coefficient2 >>! 4l <: u16) &. 255us <: u16) <: u8 in
  bit_vec_equal_intro_principle ();
  coef1, coef2, coef3 <: (u8 & u8 & u8) 
#pop-options

#push-options "--z3rlimit 160 --split_queries always"
[@@"opaque_to_smt"]
let compress_coefficients_5_
      coefficient2 coefficient1 coefficient4 coefficient3 coefficient5 coefficient7 coefficient6 coefficient8
  =
  let coef1:u8 = ((coefficient2 &. 7uy <: u8) <<! 5l <: u8) |. coefficient1 in
  let coef2:u8 =
    (((coefficient4 &. 1uy <: u8) <<! 7l <: u8) |. (coefficient3 <<! 2l <: u8) <: u8) |.
    (coefficient2 >>! 3l <: u8)
  in
  let coef3:u8 = ((coefficient5 &. 15uy <: u8) <<! 4l <: u8) |. (coefficient4 >>! 1l <: u8) in
  let coef4:u8 =
    (((coefficient7 &. 3uy <: u8) <<! 6l <: u8) |. (coefficient6 <<! 1l <: u8) <: u8) |.
    (coefficient5 >>! 4l <: u8)
  in
  let coef5:u8 = (coefficient8 <<! 3l <: u8) |. (coefficient7 >>! 2l <: u8) in
  bit_vec_equal_intro_principle ();
  coef1, coef2, coef3, coef4, coef5 <: (u8 & u8 & u8 & u8 & u8)
#pop-options

#push-options "--z3rlimit 500"
[@@"opaque_to_smt"]
let decompress_coefficients_10_ byte2 byte1 byte3 byte4 byte5 =
  let coefficient1:i32 = ((byte2 &. 3l <: i32) <<! 8l <: i32) |. (byte1 &. 255l <: i32) in
  let coefficient2:i32 = ((byte3 &. 15l <: i32) <<! 6l <: i32) |. (byte2 >>! 2l <: i32) in
  let coefficient3:i32 = ((byte4 &. 63l <: i32) <<! 4l <: i32) |. (byte3 >>! 4l <: i32) in
  let coefficient4:i32 = (byte5 <<! 2l <: i32) |. (byte4 >>! 6l <: i32) in
  lemma_get_bit_bounded' coefficient1 10;
  lemma_get_bit_bounded' coefficient2 10;
  lemma_get_bit_bounded' coefficient3 10;
  lemma_get_bit_bounded' coefficient4 10;
  bit_vec_equal_intro_principle ();
  coefficient1, coefficient2, coefficient3, coefficient4
#pop-options

#push-options "--z3rlimit 300"
[@@"opaque_to_smt"]
let decompress_coefficients_11_
      byte2 byte1 byte3 byte5 byte4 byte6 byte7 byte9 byte8 byte10 byte11 =
  let coefficient1:i32 = ((byte2 &. 7l <: i32) <<! 8l <: i32) |. byte1 in
  let coefficient2:i32 = ((byte3 &. 63l <: i32) <<! 5l <: i32) |. (byte2 >>! 3l <: i32) in
  let coefficient3:i32 =
    (((byte5 &. 1l <: i32) <<! 10l <: i32) |. (byte4 <<! 2l <: i32) <: i32) |. (byte3 >>! 6l <: i32)
  in
  let coefficient4:i32 = ((byte6 &. 15l <: i32) <<! 7l <: i32) |. (byte5 >>! 1l <: i32) in
  let coefficient5:i32 = ((byte7 &. 127l <: i32) <<! 4l <: i32) |. (byte6 >>! 4l <: i32) in
  let coefficient6:i32 =
    (((byte9 &. 3l <: i32) <<! 9l <: i32) |. (byte8 <<! 1l <: i32) <: i32) |. (byte7 >>! 7l <: i32)
  in
  let coefficient7:i32 = ((byte10 &. 31l <: i32) <<! 6l <: i32) |. (byte9 >>! 2l <: i32) in
  let coefficient8:i32 = (byte11 <<! 3l <: i32) |. (byte10 >>! 5l <: i32) in
  bit_vec_equal_intro_principle ();
  lemma_get_bit_bounded' coefficient1 11;
  lemma_get_bit_bounded' coefficient2 11;
  lemma_get_bit_bounded' coefficient3 11;
  lemma_get_bit_bounded' coefficient4 11;
  lemma_get_bit_bounded' coefficient5 11;
  lemma_get_bit_bounded' coefficient6 11;
  lemma_get_bit_bounded' coefficient7 11;
  lemma_get_bit_bounded' coefficient8 11;
  coefficient1,
  coefficient2,
  coefficient3,
  coefficient4,
  coefficient5,
  coefficient6,
  coefficient7,
  coefficient8
#pop-options

#push-options "--z3rlimit 50"
[@@"opaque_to_smt"]
let decompress_coefficients_4_ byte =
  let coefficient1:i32 = cast (byte &. 15uy <: u8) <: i32 in
  let coefficient2:i32 = cast ((byte >>! 4l <: u8) &. 15uy <: u8) <: i32 in
  lemma_get_bit_bounded' coefficient1 4;
  lemma_get_bit_bounded' coefficient2 4;
  bit_vec_equal_intro_principle ();
  coefficient1, coefficient2
#pop-options

#push-options "--z3rlimit 400"
[@@"opaque_to_smt"]
let decompress_coefficients_5_ byte1 byte2 byte3 byte4 byte5 =
  let coefficient1:i32 = byte1 &. 31l in
  let coefficient2:i32 = ((byte2 &. 3l <: i32) <<! 3l <: i32) |. (byte1 >>! 5l <: i32) in
  let coefficient3:i32 = (byte2 >>! 2l <: i32) &. 31l in
  let coefficient4:i32 = ((byte3 &. 15l <: i32) <<! 1l <: i32) |. (byte2 >>! 7l <: i32) in
  let coefficient5:i32 = ((byte4 &. 1l <: i32) <<! 4l <: i32) |. (byte3 >>! 4l <: i32) in
  let coefficient6:i32 = (byte4 >>! 1l <: i32) &. 31l in
  let coefficient7:i32 = ((byte5 &. 7l <: i32) <<! 2l <: i32) |. (byte4 >>! 6l <: i32) in
  let coefficient8:i32 = byte5 >>! 3l in
  bit_vec_equal_intro_principle ();
  lemma_get_bit_bounded' coefficient1 5;
  lemma_get_bit_bounded' coefficient2 5;
  lemma_get_bit_bounded' coefficient3 5;
  lemma_get_bit_bounded' coefficient4 5;
  lemma_get_bit_bounded' coefficient5 5;
  lemma_get_bit_bounded' coefficient6 5;
  lemma_get_bit_bounded' coefficient7 5;
  lemma_get_bit_bounded' coefficient8 5;
  coefficient1,
  coefficient2,
  coefficient3,
  coefficient4,
  coefficient5,
  coefficient6,
  coefficient7,
  coefficient8
#pop-options

let cast_bound_lemma 
  #t #u
  (n: int_t t) 
  (d: num_bits t)
  : Lemma (requires bounded n d /\ d <= bits u /\ unsigned u /\ v n >= 0)
          (ensures  bounded (cast #(int_t t) #(int_t u) n) d)
          [SMTPat (bounded n d); SMTPat (cast #(int_t t) #(int_t u) n)]
  = ()

#push-options "--z3rlimit 90"
[@@"opaque_to_smt"]
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

#restart-solver

#push-options "--fuel 0 --ifuel 1 --query_stats --z3rlimit 100"
[@@"opaque_to_smt"]
let compress_then_serialize_10_
      v_OUT_LEN
      re
    =
  let accT = t_Array u8 v_OUT_LEN in
  let inv = fun (acc: t_Array u8 v_OUT_LEN) (i: usize) -> 
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
[@@"opaque_to_smt"]
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

#push-options "--z3rlimit 220"
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

module A = Libcrux.Kem.Kyber.Arithmetic

[@@"opaque_to_smt"]
let update3 #n (s: t_Array 't n) (offset: usize {v offset + 3 <= v n}) (i0 i1 i2: 't)
  : s': t_Array 't n { Seq.index s' (v offset +  0) == i0
                    /\ Seq.index s' (v offset +  1) == i1
                    /\ Seq.index s' (v offset +  2) == i2
                    /\ (forall i. (i < v offset \/ i >= v offset + 3) ==> Seq.index s' i == Seq.index s i) }
 = let open Rust_primitives.Hax.Monomorphized_update_at in
    let s = update_at_usize s  offset           i0 in
    let s = update_at_usize s (offset +! sz  1) i1 in
    update_at_usize s (offset +! sz  2) i2

let slice_map_lemma #t #u #n (f: t -> u) (arr: t_Array t n)
  (start: nat) (len: nat {start + len <= v n})
  : Lemma (  Seq.slice (Spec.Kyber.map' f arr) start (start + len)
          == Spec.Kyber.map' f (Seq.slice arr start (start + len))
          )
  = let f_arr = Spec.Kyber.map' f arr in
    let lhs = Seq.slice f_arr start (start + len) in
    let rhs = Spec.Kyber.map' f (Seq.slice arr start (start + len)) in
    introduce forall i. Seq.index lhs i == Seq.index rhs i
    with (
      Seq.lemma_index_slice f_arr start (start + len) i;
      Seq.lemma_index_slice   arr start (start + len) i;
      let sz_i_start, sz_i = sz (i + start), sz i in
      assert (Seq.index f_arr (v sz_i_start) == f (Seq.index arr (v (sz_i_start))));
      assert (Seq.index rhs (v sz_i) == f (Seq.index (Seq.slice arr start (start + len)) (v sz_i)))
    );
    assert (Seq.equal lhs rhs)

#push-options "--z3rlimit 2800 --fuel 0 --ifuel 0 --retry 0 --split_queries no"
let serialize_uncompressed_ring_element re =
  let serialized: t_Array u8 (sz 384) = Rust_primitives.Hax.repeat 0uy (sz 384) in
  let max = v (sz 384) * 8 in
  assert (max == 256 * 12 /\ max == 384 * 8 /\ 128 * 2 * 12 == max);
  assert (128 == v (length re.f_coefficients /! (sz 2)));
  let serialized =
    Rust_primitives.Iterators.foldi_chunks_exact #_ #_ 
      #(fun serialized i -> 
        let i = v i in
        i <= 128 /\ (
            let limit = i * 2 * 12 in
            let coefficients: t_Array _ (sz 256) = Spec.Kyber.map' to_unsigned_representative re.f_coefficients in
            bit_vec_sub (bit_vec_of_int_t_array serialized   8 ) 0 limit
         == bit_vec_sub (bit_vec_of_int_t_array coefficients 12) 0 limit)
      )
      (re.A.f_coefficients <: t_Array _ (sz 256))
      (sz 2)
      serialized
      (fun serialized it -> let i, coefficients = it in

    let coefficient1 = A.to_unsigned_representative (coefficients.[ sz 0 ] <: i32) in
    let coefficient2 = A.to_unsigned_representative (coefficients.[ sz 1 ] <: i32) in
    let (coef1, coef2, coef3) = compress_coefficients_3_ coefficient1 coefficient2 in
    let j = sz 3 *! i in
    let serialized' = update3 serialized j coef1 coef2 coef3 in
    assert (      Seq.slice serialized' (v j) (v j + 3)
      `Seq.equal` Seq.slice (create3 (coef1, coef2, coef3)) 0 3);
    bit_vec_equal_intro 
        (let coefficients: t_Array _ (sz 2) = Spec.Kyber.map' to_unsigned_representative coefficients in
         bit_vec_of_int_t_array coefficients 12)
        (retype (bit_vec_sub (bit_vec_of_int_t_array serialized'   8) (3 * v i * 8) (3 * 8)));
    let full_coefficients: t_Array u16 (sz 256) = Spec.Kyber.map' to_unsigned_representative re.f_coefficients in
    slice_map_lemma #_ #u16 to_unsigned_representative re.f_coefficients (v i * 2) 2;
    bit_vec_equal_intro
        (bit_vec_sub (bit_vec_of_int_t_array serialized'   8) 0 (v i * 2 * 12))
        (bit_vec_sub (bit_vec_of_int_t_array serialized   8 ) 0 (v i * 2 * 12));
    bit_vec_equal_extend (bit_vec_of_int_t_array serialized' 8)
                         (bit_vec_of_int_t_array full_coefficients 12)
                         0 0 (v i * 2 * 12) (3 * 8);
    serialized' <: t_Array u8 (sz 384))
  in
  serialized
#pop-options

