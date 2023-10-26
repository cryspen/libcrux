module Libcrux.Kem.Kyber.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_BARRETT_SHIFT: i32 = 26l

let v_BARRETT_R: i32 = 1l <<! v_BARRETT_SHIFT

let v_BARRETT_MULTIPLIER: i32 = 20159l

let barrett_reduce (value: i32) : i32 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.(value >. ((Core.Ops.Arith.Neg.neg v_BARRETT_R <: i32) /! 2l <: i32) <: bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: value > -BARRETT_R / 2"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.(value <. (v_BARRETT_R /! 2l <: i32) <: bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: value < BARRETT_R / 2"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let quotient:i32 =
    ((value *! v_BARRETT_MULTIPLIER <: i32) +! (v_BARRETT_R >>! 1l <: i32) <: i32) >>!
    v_BARRETT_SHIFT
  in
  let reduced:i32 = value -! (quotient *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.(reduced >. (Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32)
            <:
            bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: reduced > -FIELD_MODULUS"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.(reduced <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: reduced < FIELD_MODULUS"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  reduced

let v_MONTGOMERY_SHIFT: i32 = 16l

let v_MONTGOMERY_R: i32 = 1l <<! v_MONTGOMERY_SHIFT

let v_INVERSE_OF_MODULUS_MOD_R: i32 = (-3327l)

let montgomery_reduce (value: i32) : i32 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.(value >.
            ((Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) *!
              (v_MONTGOMERY_R /! 2l <: i32)
              <:
              i32)
            <:
            bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: value > -FIELD_MODULUS * (MONTGOMERY_R / 2)"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.(value <.
            (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS *! (v_MONTGOMERY_R /! 2l <: i32) <: i32)
            <:
            bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: value < FIELD_MODULUS * (MONTGOMERY_R / 2)"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let t:i32 = (value &. (v_MONTGOMERY_R -! 1l <: i32) <: i32) *! v_INVERSE_OF_MODULUS_MOD_R in
  let t:i16 = cast (t &. (v_MONTGOMERY_R -! 1l <: i32)) <: i16 in
  let reduced:i32 =
    (value >>! v_MONTGOMERY_SHIFT <: i32) -!
    (((Core.Convert.f_from t <: i32) *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) >>!
      v_MONTGOMERY_SHIFT
      <:
      i32)
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.(reduced >. (Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32)
            <:
            bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: reduced > -FIELD_MODULUS"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.(reduced <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: reduced < FIELD_MODULUS"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  reduced

type t_KyberPolynomialRingElement = { f_coefficients:t_Array i32 (sz 256) }

let impl__KyberPolynomialRingElement__ZERO: t_KyberPolynomialRingElement =
  { f_coefficients = Rust_primitives.Hax.repeat 0l (sz 256) }

let impl_1: Core.Ops.Index.t_Index t_KyberPolynomialRingElement usize =
  {
    f_Output = i32;
    f_index
    =
    fun (self: t_KyberPolynomialRingElement) (index: usize) -> self.f_coefficients.[ index ]
  }

let impl_2: Core.Iter.Traits.Collect.t_IntoIterator t_KyberPolynomialRingElement =
  {
    f_Item = i32;
    f_IntoIter = Core.Array.Iter.t_IntoIter i32 (sz 256);
    f_into_iter
    =
    fun (self: t_KyberPolynomialRingElement) ->
      Core.Iter.Traits.Collect.f_into_iter self.f_coefficients
  }

let impl_3: Core.Ops.Arith.t_Add t_KyberPolynomialRingElement t_KyberPolynomialRingElement =
  {
    f_Output = t_KyberPolynomialRingElement;
    f_add
    =
    fun (self: t_KyberPolynomialRingElement) (other: t_KyberPolynomialRingElement) ->
      let result:t_KyberPolynomialRingElement = impl__KyberPolynomialRingElement__ZERO in
      let result:t_KyberPolynomialRingElement =
        Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                  Core.Ops.Range.f_start = sz 0;
                  Core.Ops.Range.f_end = Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
                })
            <:
            Core.Ops.Range.t_Range usize)
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
    f_Output = t_KyberPolynomialRingElement;
    f_sub
    =
    fun (self: t_KyberPolynomialRingElement) (other: t_KyberPolynomialRingElement) ->
      let result:t_KyberPolynomialRingElement = impl__KyberPolynomialRingElement__ZERO in
      let result:t_KyberPolynomialRingElement =
        Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                  Core.Ops.Range.f_start = sz 0;
                  Core.Ops.Range.f_end = Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
                })
            <:
            Core.Ops.Range.t_Range usize)
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