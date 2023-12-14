module Libcrux.Kem.Kyber.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

open Libcrux.Kem.Kyber.Arithmetic

unfold let map (f:'a -> 'b) (s: t_Array 'a 'n): t_Array 'b 'n
  = createi 'n (fun i -> f s.[i])

type bit = n: nat {n < 2}

unfold let bits_to_byte (bits: t_Array bit (sz 8)): u8
  = mk_int ( bits.[sz 0]
           + bits.[sz 1] * 2
           + bits.[sz 2] * 4
           + bits.[sz 3] * 8
           + bits.[sz 4] * 16
           + bits.[sz 5] * 32
           + bits.[sz 6] * 64
           + bits.[sz 7] * 128 )

let bits_to_bytes (#n: usize {v n < 100}) (bits: t_Array bit (n *! sz 8))
  : t_Array u8 n
  = createi n (fun i -> bits_to_byte (Seq.slice bits (8 * v i) (8 * v i + 8)))

let get_bit_nat (x: nat) (nth: nat): bit
  = (x / pow2 nth) % 2

[@"opaque_to_smt"]
let get_bit (#n: inttype) (x: int_t n) (nth: usize {v nth < bits n}): bit
  = if v x >= 0
    then get_bit_nat (v x) (v nth)
    else 
      let x' = pow2 (bits n) + v x in
      get_bit_nat x' (v nth)

type d_param n = d: usize {v d > 0 /\ v d <= bits n}

unfold let bit_and (x y: bit): bit
    = match x, y with
      | (1, 1) -> 1
      | _ -> 0
      
unfold let bit_or (x y: bit): bit
    = (x + y) % 2

let get_bit_and #t (x y: int_t t) (i: usize {v i < bits t})
  : Lemma (get_bit (x &. y) i == get_bit x i `bit_and` get_bit y i)
          [SMTPat (get_bit (x &. y) i)]
  = admit ()

let get_bit_or #t (x y: int_t t) (i: usize {v i < bits t})
  : Lemma (get_bit (x |. y) i == get_bit x i `bit_or` get_bit y i)
          [SMTPat (get_bit (x |. y) i)]
  = admit ()

let get_bit_shl #t #u (x: int_t t) (y: int_t u) (i: usize {v i < bits t})
  : Lemma
    (requires v y >= 0 /\ v y < bits t)
    (ensures get_bit (x <<! y) i == (if v i < v y
                                     then 0
                                     else get_bit x (mk_int (v i - v y))))
    [SMTPat (get_bit (x <<! y) i)]
  = admit ()

let get_bit_arr
  (#n: inttype) (#len: usize) 
  (arr: t_Array (int_t n) len)
  (d: d_param n)
  (nth: usize {v nth < v len * v d})
  : bit
  = get_bit (arr.[nth /! d]) (nth %! d)


let get_bit_arr_nat
  (#n: inttype) (#len: nat {len < max_usize})
  (arr: t_Array (int_t n) (sz len))
  (d: nat {d > 0 /\ d <= bits n}) // v d > 0 /\ v d <= bits n
  (nth: nat {nth < len * d /\ nth < max_usize})
  : bit
  = get_bit_arr arr (mk_int d) (mk_int nth)

// let bit_vector_slice (#n: inttype) (x: int_t n {v x > 0}) (d: d_param n): t_Array bit d
//   = createi d (get_bit x)

let bit_vector
  (#n: inttype) (#len: usize)
  (arr: t_Array (int_t n) len)
  (d: d_param n)
  : t_Array bit (len *. d)
  = createi (len *. d) (get_bit_arr arr d)

open MkSeq

open FStar.Tactics


let pow2_minus_one_mod_lemma1 (n: nat) (m: nat {m < n})
   : Lemma (((pow2 n - 1) / pow2 m) % 2 == 1)
   = let d: pos = n - m in
     Math.Lemmas.pow2_plus m d;
     Math.Lemmas.lemma_div_plus (-1) (pow2 d) (pow2 m);
     if d > 0 then Math.Lemmas.pow2_double_mult (d-1)

let pow2_minus_one_mod_lemma2 (n: nat) (m: nat {n <= m})
  : Lemma (((pow2 n - 1) / pow2 m) % 2 == 0)
  = Math.Lemmas.pow2_le_compat m n;
    Math.Lemmas.small_div (pow2 n - 1) (pow2 m)

let get_bit_pow2_minus_one
  #t (n: nat {pow2 n - 1 <= maxint t}) 
  (nth: usize {v nth < bits t})
  : Lemma (  get_bit (mk_int #t (pow2 n - 1)) nth
          == (if v nth < n then 1 else 0))
  = reveal_opaque (`%get_bit) (get_bit (mk_int #t (pow2 n - 1)) nth);
    if v nth < n then pow2_minus_one_mod_lemma1 n (v nth)
                 else pow2_minus_one_mod_lemma2 n (v nth)

unfold let mask_inv_opt =
  function | 0   -> Some 0
           | 1   -> Some 1
           | 3   -> Some 2
           | 7   -> Some 3
           | 15  -> Some 4
           | 31  -> Some 5
           | 63  -> Some 6
           | 127 -> Some 7
           | 255 -> Some 8
           | _   -> None

let get_bit_pow2_minus_one_i32
  (x: int {Some? (mask_inv_opt x)})
  (nth: usize {v nth < 32})
  : Lemma (
     get_bit (FStar.Int32.int_to_t x) nth == (if v nth < Some?.v (mask_inv_opt x) then 1 else 0)
  )
  [SMTPat (get_bit (FStar.Int32.int_to_t x) nth)]
  = let n = Some?.v (mask_inv_opt x) in
    mk_int_equiv_lemma #i32_inttype x;
    get_bit_pow2_minus_one #i32_inttype n nth
  
let get_bit_pow2_minus_one_u8
  (t: _ {t == u8_inttype})
  (x: int {Some? (mask_inv_opt x)})
  (nth: usize {v nth < 8})
  : Lemma (
        get_bit #t (FStar.UInt8.uint_to_t x) nth 
     == (if v nth < Some?.v (mask_inv_opt x) then 1 else 0)
  )
  [SMTPat (get_bit #t (FStar.UInt8.uint_to_t x) nth)]
  = let n = Some?.v (mask_inv_opt x) in
    mk_int_equiv_lemma #u8_inttype x;
    get_bit_pow2_minus_one #u8_inttype n nth

let get_bit_cast #t #u
  (x: int_t t) (nth: usize)
  : Lemma (requires v nth < bits u /\ v nth < bits t)
          (ensures get_bit x nth == get_bit (cast x <: int_t u) nth)
          [SMTPat (get_bit (cast #(int_t t) #(int_t u) x <: int_t u) nth)]
  = reveal_opaque (`%get_bit) (get_bit x nth);
    reveal_opaque (`%get_bit) (get_bit (cast x <: int_t u) nth);
    admit ()

let get_bit_shr #t #u (x: int_t t) (y: int_t u) (i: usize {v i < bits t})
  : Lemma 
    (requires v y >= 0 /\ v y < bits t)
    (ensures get_bit (x >>! y) i == (if v i < bits t - v y
                                     then get_bit x (mk_int (v i + v y))
                                     else 
                                       if signed t
                                       then get_bit x (mk_int (bits t - 1))
                                       else 0))
    [SMTPat (get_bit (x >>! y) i)]
  = admit ()

let get_last_bit_signed_lemma (#t: inttype{signed t}) (x: int_t t)
  : Lemma (   get_bit x (mk_int (bits t - 1)) 
          == (if v x < 0 then 1 else 0))
    [SMTPat (get_bit x (mk_int (bits t - 1)))]
  = admit ()

//each input has 10 bits
val compress_coefficients_10_ 
  (i1 i2 i3 i4: i32)
  : Pure 
    (u8 & u8 & u8 & u8 & u8)
    (requires True)
    (ensures fun tuple ->
         let inputs = get_bit_arr_nat (mk_seq4 i1 i2 i3 i4) 10 in
         let outputs = get_bit_arr_nat (mk_seq_tup5 tuple) 8 in
         forall (i: nat). i < 40 ==> inputs i == outputs i
    )
#push-options "--fuel 0 --ifuel 1 --z3rlimit 90"
let compress_coefficients_10_ (coefficient1 coefficient2 coefficient3 coefficient4: i32) =
  let coef1:u8 = cast (coefficient1 &. 255l <: i32) <: u8 in // coefficient1[0-8]
  let coef2:u8 =
    ((cast (coefficient2 &. 63l <: i32) <: u8) <<! 2l <: u8) |.
    (cast ((coefficient1 >>! 8l <: i32) &. 3l <: i32) <: u8) // 8-10
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
  let result = coef1, coef2, coef3, coef4, coef5 <: (u8 & u8 & u8 & u8 & u8) in
  result
#pop-options

let int_t_b t (d: d_param t) = n: int_t t {forall (i: usize). (v i < bits t /\ v i >= v d) ==> get_bit n i == 0}

// each input has 11 bits
val compress_coefficients_11_ 
  (i1 i2 i3 i4 i5 i6 i7 i8: int_t_b i32_inttype (sz 11))
  : Pure 
    (u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8)
    (requires True)
    (ensures fun tuple ->
      let _ = mk_seq8 #i32 i1 i2 i3 i4 i5 i6 i7 i8 in
         let inputs = get_bit_arr_nat (mk_seq8 i1 i2 i3 i4 i5 i6 i7 i8) 11 in
         let outputs = get_bit_arr_nat (mk_seq_tup11 tuple) 8 in
         forall (i: nat). i < 88 ==> inputs i == outputs i
    )
#push-options "--fuel 0 --ifuel 1 --z3rlimit 300"
let compress_coefficients_11_
      (coefficient1 coefficient2 coefficient3 coefficient4 coefficient5 coefficient6 coefficient7 coefficient8:
          int_t_b i32_inttype (sz 11))
    : (u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8) =
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
  coef1, coef2, coef3, coef4, coef5, coef6, coef7, coef8, coef9, coef10, coef11
  <:
  (u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8)
#pop-options

val compress_coefficients_2_ 
  (i1 i2: int_t_b u16_inttype (sz 12))
  : Pure 
    (u8 & u8 & u8)
    (requires True)
    (ensures fun tuple ->
         let inputs = get_bit_arr_nat (mk_seq2 i1 i2) 12 in
         let outputs = get_bit_arr_nat (mk_seq_tup3 tuple) 8 in
         forall (i: nat). i < 24 ==> inputs i == outputs i
    )
let compress_coefficients_3_ (coefficient1 coefficient2: u16) : (u8 & u8 & u8) =
  let coef1:u8 = cast (coefficient1 &. 255us <: u16) <: u8 in
  let coef2:u8 =
    cast ((coefficient1 >>! 8l <: u16) |. ((coefficient2 &. 15us <: u16) <<! 4l <: u16) <: u16)
    <:
    u8
  in
  let coef3:u8 = cast ((coefficient2 >>! 4l <: u16) &. 255us <: u16) <: u8 in
  coef1, coef2, coef3 <: (u8 & u8 & u8)

val compress_coefficients_5_ 
  (i2 i1 i4 i3 i5 i7 i6 i8: int_t_b u8_inttype (sz 5))
  : Pure 
    (u8 & u8 & u8 & u8 & u8)
    (requires True)
    (ensures fun tuple ->
         let inputs = get_bit_arr_nat (mk_seq8 i1 i2 i3 i4 i5 i6 i7 i8) 5 in
         let outputs = get_bit_arr_nat (mk_seq_tup5 tuple) 8 in
         forall (i: nat). i < 40 ==> inputs i == outputs i
    )
#push-options "--fuel 0 --ifuel 1 --z3rlimit 160"
let compress_coefficients_5_
      (coefficient2 coefficient1 coefficient4 coefficient3 coefficient5 coefficient7 coefficient6 coefficient8:
          int_t_b u8_inttype (sz 5))
    : (u8 & u8 & u8 & u8 & u8) =
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
  coef1, coef2, coef3, coef4, coef5 <: (u8 & u8 & u8 & u8 & u8)
#pop-options

val decompress_coefficients_10_
  (i2 i1 i3 i4 i5: int_t_b i32_inttype (sz 8))
  : Pure 
    (i32 & i32 & i32 & i32)
    (requires True)
    (ensures fun tuple ->
         let inputs = get_bit_arr_nat (mk_seq5 i1 i2 i3 i4 i5) 8 in
         let outputs = get_bit_arr_nat (mk_seq_tup4 tuple) 10 in
         forall (i: nat). i < 40 ==> inputs i == outputs i
    )
#push-options "--fuel 0 --ifuel 1 --z3rlimit 160"
let decompress_coefficients_10_ (byte2 byte1 byte3 byte4 byte5: int_t_b i32_inttype (sz 8)) : (i32 & i32 & i32 & i32) =
  let coefficient1:i32 = ((byte2 &. 3l <: i32) <<! 8l <: i32) |. (byte1 &. 255l <: i32) in
  let coefficient2:i32 = ((byte3 &. 15l <: i32) <<! 6l <: i32) |. (byte2 >>! 2l <: i32) in
  let coefficient3:i32 = ((byte4 &. 63l <: i32) <<! 4l <: i32) |. (byte3 >>! 4l <: i32) in
  let coefficient4:i32 = (byte5 <<! 2l <: i32) |. (byte4 >>! 6l <: i32) in
  coefficient1, coefficient2, coefficient3, coefficient4 <: (i32 & i32 & i32 & i32)
#pop-options

val decompress_coefficients_11_
  (i2 i1 i3 i5 i4 i6 i7 i9 i8 i10 i11: int_t_b i32_inttype (sz 8))
  : Pure 
    (i32 & i32 & i32 & i32 & i32 & i32 & i32 & i32)
    (requires True)
    (ensures fun tuple ->
         let inputs = get_bit_arr_nat (mk_seq11 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11) 8 in
         let outputs = get_bit_arr_nat (mk_seq_tup8 tuple) 11 in
         forall (i: nat). i < 88 ==> inputs i == outputs i
    )
#push-options "--fuel 0 --ifuel 1 --z3rlimit 260"
let decompress_coefficients_11_
      (byte2 byte1 byte3 byte5 byte4 byte6 byte7 byte9 byte8 byte10 byte11: int_t_b i32_inttype (sz 8))
    : (i32 & i32 & i32 & i32 & i32 & i32 & i32 & i32) =
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
  coefficient1,
  coefficient2,
  coefficient3,
  coefficient4,
  coefficient5,
  coefficient6,
  coefficient7,
  coefficient8
  <:
  (i32 & i32 & i32 & i32 & i32 & i32 & i32 & i32)
#pop-options


val decompress_coefficients_4_
  (i1: u8)
  : Pure 
    (i32 & i32)
    (requires True)
    (ensures fun tuple ->
         let inputs = get_bit_arr_nat (mk_seq1 i1) 8 in
         let outputs = get_bit_arr_nat (mk_seq_tup2 tuple) 4 in
         forall (i: nat). i < 4 ==> inputs i == outputs i
    )
#push-options "--fuel 0 --ifuel 1 --z3rlimit 40"
let decompress_coefficients_4_ (byte: u8) : (i32 & i32) =
  let coefficient1:i32 = cast (byte &. 15uy <: u8) <: i32 in
  let coefficient2:i32 = cast ((byte >>! 4l <: u8) &. 15uy <: u8) <: i32 in
  coefficient1, coefficient2 <: (i32 & i32)
#pop-options

val decompress_coefficients_5_
  (i1 i2 i3 i4 i5: int_t_b i32_inttype (sz 5))
  : Pure 
    (i32 & i32 & i32 & i32 & i32 & i32 & i32 & i32)
    (requires True)
    (ensures fun tuple ->
         let inputs = get_bit_arr_nat (mk_seq5 i1 i2 i3 i4 i5) 8 in
         let outputs = get_bit_arr_nat (mk_seq_tup8 tuple) 5 in
         forall (i: nat). i < 40 ==> inputs i == outputs i
    )
#push-options "--fuel 0 --ifuel 1 --z3rlimit 90"
let decompress_coefficients_5_ (byte1 byte2 byte3 byte4 byte5: int_t_b i32_inttype (sz 5))
    : (i32 & i32 & i32 & i32 & i32 & i32 & i32 & i32) =
  let coefficient1:i32 = byte1 &. 31l in
  let coefficient2:i32 = ((byte2 &. 3l <: i32) <<! 3l <: i32) |. (byte1 >>! 5l <: i32) in
  let coefficient3:i32 = (byte2 >>! 2l <: i32) &. 31l in
  let coefficient4:i32 = ((byte3 &. 15l <: i32) <<! 1l <: i32) |. (byte2 >>! 7l <: i32) in
  let coefficient5:i32 = ((byte4 &. 1l <: i32) <<! 4l <: i32) |. (byte3 >>! 4l <: i32) in
  let coefficient6:i32 = (byte4 >>! 1l <: i32) &. 31l in
  let coefficient7:i32 = ((byte5 &. 7l <: i32) <<! 2l <: i32) |. (byte4 >>! 6l <: i32) in
  let coefficient8:i32 = byte5 >>! 3l in
  coefficient1,
  coefficient2,
  coefficient3,
  coefficient4,
  coefficient5,
  coefficient6,
  coefficient7,
  coefficient8
  <:
  (i32 & i32 & i32 & i32 & i32 & i32 & i32 & i32)
#pop-options

let compress_then_serialize_10_
      (v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : t_Array u8 v_OUT_LEN =
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:t_Array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    t_Slice i32)
                  (sz 4)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUT_LEN = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
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

let compress_then_serialize_11_
      (v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : t_Array u8 v_OUT_LEN =
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:t_Array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    t_Slice i32)
                  (sz 8)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUT_LEN = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let coefficient1:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 0 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient2:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 1 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient3:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 2 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient4:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 3 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient5:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 4 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient6:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 5 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient7:i32 =
            Libcrux.Kem.Kyber.Compress.compress_ciphertext_coefficient 11uy
              (Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 6 ] <: i32
                  )
                <:
                u16)
          in
          let coefficient8:i32 =
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

let compress_then_serialize_4_
      (v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : t_Array u8 v_OUT_LEN =
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:t_Array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    t_Slice i32)
                  (sz 2)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUT_LEN = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
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
      (v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : t_Array u8 v_OUT_LEN =
  let serialized:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let serialized:t_Array u8 v_OUT_LEN =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    t_Slice i32)
                  (sz 8)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUT_LEN = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
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

let compress_then_serialize_message (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
  let serialized:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let serialized:t_Array u8 (sz 32) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    t_Slice i32)
                  (sz 8)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 (sz 32) = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
                    (Core.Slice.impl__iter coefficients <: Core.Slice.Iter.t_Iter i32)
                  <:
                  Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter i32))
              <:
              Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter i32))
            serialized
            (fun serialized temp_1_ ->
                let serialized:t_Array u8 (sz 32) = serialized in
                let j, coefficient:(usize & i32) = temp_1_ in
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
  serialized

let compress_then_serialize_ring_element_u #p
      (v_COMPRESSION_FACTOR v_OUT_LEN: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
  let _:Prims.unit = () <: Prims.unit in
  Rust_primitives.Integers.mk_int_equiv_lemma #u32_inttype (v v_COMPRESSION_FACTOR);
  match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
  | 10ul -> compress_then_serialize_10_ v_OUT_LEN re
  | 11ul -> compress_then_serialize_11_ v_OUT_LEN re
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)


let compress_then_serialize_ring_element_v #p v_COMPRESSION_FACTOR v_OUT_LEN re =
  let _:Prims.unit = () <: Prims.unit in
  Rust_primitives.Integers.mk_int_equiv_lemma #u32_inttype (v v_COMPRESSION_FACTOR);
  let res = 
  match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
  | 4ul -> compress_then_serialize_4_ v_OUT_LEN re
  | 5ul -> compress_then_serialize_5_ v_OUT_LEN re
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)
  in
  admit(); //P-F
  res

#push-options "--z3rlimit 150 --max_ifuel 2" 
let deserialize_then_decompress_10_ (serialized: t_Slice u8)
    : Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
  let _:Prims.unit = () <: Prims.unit in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 5) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          assume (length bytes == sz 5);
          let byte1:i32 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
          let byte2:i32 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
          let byte3:i32 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
          let byte4:i32 = cast (bytes.[ sz 3 ] <: u8) <: i32 in
          let byte5:i32 = cast (bytes.[ sz 4 ] <: u8) <: i32 in
          let coefficient1, coefficient2, coefficient3, coefficient4:(i32 & i32 & i32 & i32) =
            decompress_coefficients_10_ byte2 byte1 byte3 byte4 byte5
          in
          assume (v i * 4 + 4 <= 256);
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 10uy coefficient1);
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 10uy coefficient2);
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 10uy coefficient3);
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 10uy coefficient4);
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
         
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          re)
  in
  re

let deserialize_then_decompress_11_ (serialized: t_Slice u8)
    : Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
  let _:Prims.unit = () <: Prims.unit in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 11) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          assume (length bytes == sz 11);
          assume (v i * 8 + 8 <= 256);
          let byte1:i32 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
          let byte2:i32 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
          let byte3:i32 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
          let byte4:i32 = cast (bytes.[ sz 3 ] <: u8) <: i32 in
          let byte5:i32 = cast (bytes.[ sz 4 ] <: u8) <: i32 in
          let byte6:i32 = cast (bytes.[ sz 5 ] <: u8) <: i32 in
          let byte7:i32 = cast (bytes.[ sz 6 ] <: u8) <: i32 in
          let byte8:i32 = cast (bytes.[ sz 7 ] <: u8) <: i32 in
          let byte9:i32 = cast (bytes.[ sz 8 ] <: u8) <: i32 in
          let byte10:i32 = cast (bytes.[ sz 9 ] <: u8) <: i32 in
          let byte11:i32 = cast (bytes.[ sz 10 ] <: u8) <: i32 in
          let
          coefficient1,
          coefficient2,
          coefficient3,
          coefficient4,
          coefficient5,
          coefficient6,
          coefficient7,
          coefficient8:(i32 & i32 & i32 & i32 & i32 & i32 & i32 & i32) =
            decompress_coefficients_11_ byte2 byte1 byte3 byte5 byte4 byte6 byte7 byte9 byte8 byte10
              byte11
          in
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 11uy coefficient1);
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 11uy coefficient2);
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 11uy coefficient3);
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 11uy coefficient4);
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 11uy coefficient5);
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 11uy coefficient6);
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 11uy coefficient7);
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 11uy coefficient8);
          let coefficient1 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient1 in
          let coefficient2 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient2 in
          let coefficient3 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient3 in
          let coefficient4 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient4 in
          let coefficient5 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient5 in
          let coefficient6 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient6 in
          let coefficient7 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient7 in
          let coefficient8 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 11uy coefficient8 in
          
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          re)
  in
  re

let deserialize_then_decompress_4_ (serialized: t_Slice u8)
    : Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
  let _:Prims.unit = () <: Prims.unit in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__iter serialized <: Core.Slice.Iter.t_Iter u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
          let i, byte:(usize & u8) = temp_1_ in
          assume (v i * 2 + 2 <= 256);
          let coefficient1, coefficient2:(i32 & i32) = decompress_coefficients_4_ byte in
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 4uy coefficient1);
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 4uy coefficient2);
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          re)
  in
  re

let deserialize_then_decompress_5_ (serialized: t_Slice u8)
    : Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
  let _:Prims.unit = () <: Prims.unit in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 5) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          assume (length bytes = sz 5);
          assume (v i * 8 + 8 <= 256);
          let byte1:i32 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
          let byte2:i32 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
          let byte3:i32 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
          let byte4:i32 = cast (bytes.[ sz 3 ] <: u8) <: i32 in
          let byte5:i32 = cast (bytes.[ sz 4 ] <: u8) <: i32 in
          let
          coefficient1,
          coefficient2,
          coefficient3,
          coefficient4,
          coefficient5,
          coefficient6,
          coefficient7,
          coefficient8:(i32 & i32 & i32 & i32 & i32 & i32 & i32 & i32) =
            decompress_coefficients_5_ byte1 byte2 byte3 byte4 byte5
          in
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 5uy coefficient1);
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 5uy coefficient1);
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 5uy coefficient2);
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 5uy coefficient3);
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 5uy coefficient4);
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 5uy coefficient5);
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 5uy coefficient6);
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 5uy coefficient7);
          assume (Libcrux.Kem.Kyber.Compress.decompress_pre 5uy coefficient8);
          let coefficient1 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient1 in
          let coefficient2 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient2 in
          let coefficient3 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient3 in
          let coefficient4 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient4 in
          let coefficient5 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient5 in
          let coefficient6 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient6 in
          let coefficient7 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient7 in
          let coefficient8 = Libcrux.Kem.Kyber.Compress.decompress_ciphertext_coefficient 5uy coefficient8 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          admit();
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          re)
  in
  re
#pop-options

let deserialize_then_decompress_message (serialized: t_Array u8 (sz 32)) =
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__iter (Rust_primitives.unsize serialized <: t_Slice u8)
                <:
                Core.Slice.Iter.t_Iter u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
          let i, byte:(usize & u8) = temp_1_ in
          assume (i <. sz 32);
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
                let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
                let j:usize = j in
                let coefficient_compressed:i32 = cast ((byte >>! j <: u8) &. 1uy <: u8) <: i32 in
                assume (coefficient_compressed =. 0l || coefficient_compressed =. 1l);
                let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
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
                  Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
                in
                re)
          <:
          Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
  in
  admit(); //P-F
  re

let deserialize_then_decompress_ring_element_u v_COMPRESSION_FACTOR serialized = 
  let _:Prims.unit = () <: Prims.unit in
  mk_int_equiv_lemma #u32_inttype (v v_COMPRESSION_FACTOR);
  match cast (v_COMPRESSION_FACTOR <: usize) <: u32 with
  | 10ul -> deserialize_then_decompress_10_ serialized
  | 11ul -> deserialize_then_decompress_11_ serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let deserialize_then_decompress_ring_element_v v_COMPRESSION_FACTOR serialized =
  let _:Prims.unit = () <: Prims.unit in
  assert (v v_COMPRESSION_FACTOR == 4 \/ v v_COMPRESSION_FACTOR == 5);
  mk_int_equiv_lemma #u32_inttype (v v_COMPRESSION_FACTOR);
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

let deserialize_to_uncompressed_ring_element (serialized: t_Slice u8) = 
  let _:Prims.unit = () <: Prims.unit in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact serialized (sz 3) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      re
      (fun re temp_1_ ->
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = re in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          assume (length bytes = sz 3);
          assume (v i * 2 + 2 <= 256);
          let byte1:i32 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
          let byte2:i32 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
          let byte3:i32 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 2 *! i <: usize)
                (((byte2 &. 15l <: i32) <<! 8l <: i32) |. (byte1 &. 255l <: i32) <: i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 2 *! i <: usize) +! sz 1 <: usize)
                ((byte3 <<! 4l <: i32) |. ((byte2 >>! 4l <: i32) &. 15l <: i32) <: i32)
            }
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
          in
          re)
  in
  re

let serialize_uncompressed_ring_element (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement) =
  let serialized:t_Array u8 (sz 384) = Rust_primitives.Hax.repeat 0uy (sz 384) in
  let serialized:t_Array u8 (sz 384) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    t_Slice i32)
                  (sz 2)
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 (sz 384) = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let coefficient1:u16 =
            Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 0 ] <: i32)
          in
          let coefficient2:u16 =
            Libcrux.Kem.Kyber.Arithmetic.to_unsigned_representative (coefficients.[ sz 1 ] <: i32)
          in
          let coef1, coef2, coef3:(u8 & u8 & u8) =
            compress_coefficients_3_ coefficient1 coefficient2
          in
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
