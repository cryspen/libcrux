module Libcrux.Kem.Kyber.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

unfold
let t_KyberFieldElement = i32

let v_BARRETT_MULTIPLIER: i64 = 20159L

let v_BARRETT_SHIFT: i64 = 26L

let v_BARRETT_R: i64 = 1L <<! v_BARRETT_SHIFT

let v_INVERSE_OF_MODULUS_MOD_R: i32 = (-3327l)

let v_MONTGOMERY_SHIFT: u8 = 16uy

let v_MONTGOMERY_R: i32 = 1l <<! v_MONTGOMERY_SHIFT

let get_montgomery_r_least_significant_bits (value: i32)
    : Prims.Pure u16
      Prims.l_True
      (ensures
        fun result ->
          let result:u16 = result in
          result <. (Core.Num.impl__u16__pow 2us (cast (v_MONTGOMERY_SHIFT <: u8) <: u32) <: u16)) =
  cast (value &. ((1l <<! v_MONTGOMERY_SHIFT <: i32) -! 1l <: i32) <: i32) <: u16

let barrett_reduce (value: i32)
    : Prims.Pure i32
      (requires
        (Core.Convert.f_from value <: i64) >.
        (Core.Ops.Arith.Neg.neg (v_BARRETT_R /! 2L <: i64) <: i64) &&
        (Core.Convert.f_from value <: i64) <. (v_BARRETT_R /! 2L <: i64))
      (ensures
        fun result ->
          let result:i32 = result in
          result >. (Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) &&
          result <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS) =
  let t:i64 =
    ((Core.Convert.f_from value <: i64) *! v_BARRETT_MULTIPLIER <: i64) +!
    (v_BARRETT_R >>! 1l <: i64)
  in
  let quotient:i32 = cast (t >>! v_BARRETT_SHIFT <: i64) <: i32 in
  value -! (quotient *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32)

let montgomery_reduce (value: i32)
    : Prims.Pure i32
      (requires
        value >=.
        ((Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) *!
          v_MONTGOMERY_R
          <:
          i32) &&
        value <=. (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS *! v_MONTGOMERY_R <: i32))
      (ensures
        fun result ->
          let result:i32 = result in
          result >=.
          ((Core.Ops.Arith.Neg.neg (3l *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: i32
            ) /!
            2l
            <:
            i32) &&
          result <=. ((3l *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) /! 2l <: i32)) =
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

let to_unsigned_representative (fe: i32)
    : Prims.Pure u16
      (requires
        fe >=. (Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) &&
        fe <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS)
      (ensures
        fun result ->
          let result:u16 = result in
          result >=. 0us &&
          result <. (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u16)) =
  let _:Prims.unit = () <: Prims.unit in
  cast (fe +! (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &. (fe >>! 31l <: i32) <: i32) <: i32)
  <:
  u16

type t_KyberPolynomialRingElement = { f_coefficients:t_Array i32 (sz 256) }

let impl__KyberPolynomialRingElement__ZERO: t_KyberPolynomialRingElement =
  { f_coefficients = Rust_primitives.Hax.repeat 0l (sz 256) } <: t_KyberPolynomialRingElement

let add_to_ring_element (v_K: usize) (lhs rhs: t_KyberPolynomialRingElement)
    : t_KyberPolynomialRingElement =
  let _:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = () <: Prims.unit in
  let lhs:t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end
              =
              Core.Slice.impl__len (Rust_primitives.unsize lhs.f_coefficients <: t_Slice i32)
              <:
              usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      lhs
      (fun lhs i ->
          let lhs:t_KyberPolynomialRingElement = lhs in
          let i:usize = i in
          {
            lhs with
            f_coefficients
            =
            Rust_primitives.Hax.update_at lhs.f_coefficients
              i
              ((lhs.f_coefficients.[ i ] <: i32) +! (rhs.f_coefficients.[ i ] <: i32) <: i32)
            <:
            t_Array i32 (sz 256)
          }
          <:
          t_KyberPolynomialRingElement)
  in
  let _:Prims.unit = () <: Prims.unit in
  lhs