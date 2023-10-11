module Libcrux.Kem.Kyber.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_BARRETT_SHIFT: i32 = 26l

let v_BARRETT_R: i32 = 1l <<! v_BARRETT_SHIFT

let v_BARRETT_MULTIPLIER: i32 = 20159l

let barrett_reduce (value: i32) : i32 =
  let quotient:i32 =
    ((value *! v_BARRETT_MULTIPLIER <: i32) +! (v_BARRETT_R >>! 1l <: i32) <: i32) >>!
    v_BARRETT_SHIFT
  in
  value -! (quotient *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32)

let v_MONTGOMERY_SHIFT: i64 = 16L

let v_MONTGOMERY_R: i64 = 1L <<! v_MONTGOMERY_SHIFT

let v_INVERSE_OF_MODULUS_MOD_R: i64 = (-3327L)

let montgomery_reduce (value: i32) : i32 =
  let (t: i64):i64 = (Core.Convert.f_from value <: i64) *! v_INVERSE_OF_MODULUS_MOD_R in
  let (t: i32):i32 = cast (t &. (v_MONTGOMERY_R -! 1L <: i64)) <: i32 in
  (value -! (t *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: i32) >>! v_MONTGOMERY_SHIFT

let to_montgomery_domain (value: i32) : i32 = montgomery_reduce (1353l *! value <: i32)

type t_KyberPolynomialRingElement = { f_coefficients:array i32 (sz 256) }

let impl__ZERO: t_KyberPolynomialRingElement =
  { f_coefficients = Rust_primitives.Hax.repeat 0l (sz 256) }

let impl_1: Core.Ops.Index.t_Index t_KyberPolynomialRingElement usize =
  {
    f_impl_1__Output = i32;
    f_impl_1__index
    =
    fun (self: t_KyberPolynomialRingElement) (index: usize) -> self.f_coefficients.[ index ]
  }

let impl_2: Core.Iter.Traits.Collect.t_IntoIterator t_KyberPolynomialRingElement =
  {
    f_impl_2__Item = i32;
    f_impl_2__IntoIter = Core.Array.Iter.t_IntoIter i32 (sz 256);
    f_impl_2__into_iter
    =
    fun (self: t_KyberPolynomialRingElement) ->
      Core.Iter.Traits.Collect.f_into_iter self.f_coefficients
  }

let impl_3: Core.Ops.Arith.t_Add t_KyberPolynomialRingElement t_KyberPolynomialRingElement =
  {
    f_impl_3__Output = t_KyberPolynomialRingElement;
    f_impl_3__add
    =
    fun (self: t_KyberPolynomialRingElement) (other: t_KyberPolynomialRingElement) ->
      let result:t_KyberPolynomialRingElement = impl__ZERO in
      let result:t_KyberPolynomialRingElement =
        Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
                  Core.Ops.Range.f_start = sz 0;
                  Core.Ops.Range.f_end = Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
                })
            <:
            (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
          result
          (fun result i ->
              {
                result with
                f_coefficients
                =
                Rust_primitives.Hax.update_at result.f_coefficients
                  i
                  ((self.f_coefficients.[ i ] <: i32) +! (other.f_coefficients.[ i ] <: i32) <: i32)
                <:
                t_KyberPolynomialRingElement
              })
      in
      result
  }

let impl_4: Core.Ops.Arith.t_Sub t_KyberPolynomialRingElement t_KyberPolynomialRingElement =
  {
    f_impl_4__Output = t_KyberPolynomialRingElement;
    f_impl_4__sub
    =
    fun (self: t_KyberPolynomialRingElement) (other: t_KyberPolynomialRingElement) ->
      let result:t_KyberPolynomialRingElement = impl__ZERO in
      let result:t_KyberPolynomialRingElement =
        Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
                  Core.Ops.Range.f_start = sz 0;
                  Core.Ops.Range.f_end = Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
                })
            <:
            (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
          result
          (fun result i ->
              {
                result with
                f_coefficients
                =
                Rust_primitives.Hax.update_at result.f_coefficients
                  i
                  ((self.f_coefficients.[ i ] <: i32) -! (other.f_coefficients.[ i ] <: i32) <: i32)
                <:
                t_KyberPolynomialRingElement
              })
      in
      result
  }