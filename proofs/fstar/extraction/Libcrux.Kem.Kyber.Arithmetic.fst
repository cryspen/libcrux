module Libcrux.Kem.Kyber.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_BARRETT_SHIFT: i32 = 26l

let v_BARRETT_R: i32 = 1l <<! v_BARRETT_SHIFT

let v_BARRETT_MULTIPLIER: i32 = 20159l

let barrett_reduce (value: i32)
    : Prims.Pure i32
      (requires value >=. (-106527l) && value <=. 104862l)
      (ensures
        fun result ->
          result >. (Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) &&
          result <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS) =
  let quotient:i32 =
    ((value *! v_BARRETT_MULTIPLIER <: i32) +! (v_BARRETT_R >>! 1l <: i32) <: i32) >>!
    v_BARRETT_SHIFT
  in
  value -! (quotient *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32)

let v_MONTGOMERY_SHIFT: i32 = 16l

let v_MONTGOMERY_R: i32 = 1l <<! v_MONTGOMERY_SHIFT

let v_INVERSE_OF_MODULUS_MOD_R: i32 = (-3327l)

let montgomery_reduce (value: i32)
    : Prims.Pure i32
      (requires
        value >.
        (((Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) *!
            v_MONTGOMERY_R
            <:
            i32) /!
          2l
          <:
          i32) &&
        value <.
        ((Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS *! v_MONTGOMERY_R <: i32) /! 2l <: i32))
      (ensures
        fun result ->
          result >. (Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) &&
          result <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS) =
  let k:i32 = (value &. (v_MONTGOMERY_R -! 1l <: i32) <: i32) *! v_INVERSE_OF_MODULUS_MOD_R in
  let k:i16 = cast (k &. (v_MONTGOMERY_R -! 1l <: i32)) <: i16 in
  let c:i32 =
    ((Core.Convert.f_from k <: i32) *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) >>!
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
          result >=. 0us &&
          (Core.Convert.f_from result <: i32) <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS) =
  cast (fe +! ((fe >>! 15l <: i32) &. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32)) <: u16

type t_KyberPolynomialRingElement = { f_coefficients:t_Array i32 (sz 256) }

let impl__KyberPolynomialRingElement__ZERO: t_KyberPolynomialRingElement =
  { f_coefficients = Rust_primitives.Hax.repeat 0l (sz 256) }

let add_to_ring_element (lhs rhs: t_KyberPolynomialRingElement) : t_KyberPolynomialRingElement =
  let lhs:t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end
              =
              Core.Slice.impl__len (Rust_primitives.unsize lhs.f_coefficients <: t_Slice i32)
              <:
              usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      lhs
      (fun lhs i ->
          {
            lhs with
            f_coefficients
            =
            Rust_primitives.Hax.update_at lhs.f_coefficients
              i
              ((lhs.f_coefficients.[ i ] <: i32) +! (rhs.f_coefficients.[ i ] <: i32) <: i32)
            <:
            t_Array i32 (sz 256)
          })
  in
  lhs