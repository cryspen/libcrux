module Libcrux.Kem.Kyber.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_KyberFieldElement = i32

let v_BARRETT_MULTIPLIER: i64 = 20159L

let v_BARRETT_SHIFT: i64 = 26L

let v_BARRETT_R: i64 = 1L <<! v_BARRETT_SHIFT

let v_INVERSE_OF_MODULUS_MOD_R: i32 = (-3327l)

let v_MONTGOMERY_SHIFT: u8 = 16uy

let v_MONTGOMERY_R: i32 = 1l <<! v_MONTGOMERY_SHIFT

let get_montgomery_r_least_significant_bits (value: i32) : u16 =
  cast (value &. ((1l <<! v_MONTGOMERY_SHIFT <: i32) -! 1l <: i32) <: i32) <: u16

let barrett_reduce (value: i32) : i32 =
  let t:i64 =
    ((Core.Convert.f_from value <: i64) *! v_BARRETT_MULTIPLIER <: i64) +!
    (v_BARRETT_R >>! 1l <: i64)
  in
  let quotient:i32 = cast (t >>! v_BARRETT_SHIFT <: i64) <: i32 in
  value -! (quotient *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32)

let montgomery_reduce (value: i32) : i32 =
  let _:Prims.unit = () <: Prims.unit in
  let k:i32 =
    (cast (get_montgomery_r_least_significant_bits value <: u16) <: i32) *!
    v_INVERSE_OF_MODULUS_MOD_R
  in
  let k:i16 = cast (get_montgomery_r_least_significant_bits k <: u16) <: i16 in
  let c:i32 =
    ((cast (k <: i16) <: i32) *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) >>!
    v_MONTGOMERY_SHIFT
  in
  let value_high:i32 = value >>! v_MONTGOMERY_SHIFT in
  value_high -! c

let to_unsigned_representative (fe: i32) : u16 =
  let _:Prims.unit = () <: Prims.unit in
  cast (fe +! (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &. (fe >>! 31l <: i32) <: i32) <: i32)
  <:
  u16

type t_KyberPolynomialRingElement = { f_coefficients:t_Array i32 (sz 256) }

let impl__KyberPolynomialRingElement__ZERO: t_KyberPolynomialRingElement =
  { f_coefficients = Rust_primitives.Hax.repeat 0l (sz 256) } <: t_KyberPolynomialRingElement

let add_to_ring_element (v_K: usize) (lhs rhs: t_KyberPolynomialRingElement)
    : FStar.HyperStack.ST.St Prims.unit =
  Rust_primitives.f_for_loop (sz 0)
    (Core.Slice.impl__len (Rust_primitives.unsize lhs.f_coefficients <: t_Slice i32) <: usize)
    (fun i ->
        let i:usize = i in
        Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize lhs.f_coefficients
          i
          ((lhs.f_coefficients.[ i ] <: i32) +! (rhs.f_coefficients.[ i ] <: i32) <: i32)
        <:
        Prims.unit)
