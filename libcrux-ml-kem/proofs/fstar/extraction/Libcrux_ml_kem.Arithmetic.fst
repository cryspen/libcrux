module Libcrux_ml_kem.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let get_n_least_significant_bits (n: u8) (value: u32) = value &. ((1ul <<! n <: u32) -! 1ul <: u32)

let v__to_unsigned_representative (fe: i32) =
  cast (fe +! (Libcrux_ml_kem.Constants.v_FIELD_MODULUS &. (fe >>! 31l <: i32) <: i32) <: i32)
  <:
  u16

let barrett_reduce (value: i32) =
  let t:i64 =
    ((Core.Convert.f_from value <: i64) *! v_BARRETT_MULTIPLIER <: i64) +!
    (v_BARRETT_R >>! 1l <: i64)
  in
  let quotient:i32 = cast (t >>! v_BARRETT_SHIFT <: i64) <: i32 in
  value -! (quotient *! Libcrux_ml_kem.Constants.v_FIELD_MODULUS <: i32)

let montgomery_reduce (value: i32) =
  let _:i32 = v_MONTGOMERY_R in
  let t:u32 =
    (get_n_least_significant_bits v_MONTGOMERY_SHIFT (cast (value <: i32) <: u32) <: u32) *!
    v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
  in
  let k:i16 = cast (get_n_least_significant_bits v_MONTGOMERY_SHIFT t <: u32) <: i16 in
  let k_times_modulus:i32 = (cast (k <: i16) <: i32) *! Libcrux_ml_kem.Constants.v_FIELD_MODULUS in
  let c:i32 = k_times_modulus >>! v_MONTGOMERY_SHIFT in
  let value_high:i32 = value >>! v_MONTGOMERY_SHIFT in
  value_high -! c

let v__to_standard_domain (mfe: i32) =
  montgomery_reduce (mfe *! v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS <: i32)

let montgomery_multiply_fe_by_fer (fe fer: i32) = montgomery_reduce (fe *! fer <: i32)

let ntt_multiply_binomials (a0, a1: (i32 & i32)) (b0, b1: (i32 & i32)) (zeta: i32) =
  montgomery_reduce ((a0 *! b0 <: i32) +!
      ((montgomery_reduce (a1 *! b1 <: i32) <: i32) *! zeta <: i32)
      <:
      i32),
  montgomery_reduce ((a0 *! b1 <: i32) +! (a1 *! b0 <: i32) <: i32)
  <:
  (i32 & i32)
