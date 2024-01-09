module Libcrux.Kem.Kyber.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_FieldElement = i32

unfold
let t_FieldElementTimesMontgomeryR = i32

unfold
let t_MontgomeryFieldElement = i32

let v_BARRETT_MULTIPLIER: i64 = 20159L

let v_BARRETT_SHIFT: i64 = 26L

let v_BARRETT_R: i64 = 1L <<! v_BARRETT_SHIFT

let v_INVERSE_OF_MODULUS_MOD_R: u32 = 62209ul

let v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i32 = 1353l

let v_MONTGOMERY_SHIFT: u8 = 16uy

let v_MONTGOMERY_R: i32 = 1l <<! v_MONTGOMERY_SHIFT

let get_n_least_significant_bits (n: u8) (value: u32)
    : Prims.Pure u32
      (requires n =. 4uy || n =. 5uy || n =. 10uy || n =. 11uy || n =. v_MONTGOMERY_SHIFT)
      (ensures
        fun result ->
          let result:u32 = result in
          result <. (Core.Num.impl__u32__pow 2ul (Core.Convert.f_into n <: u32) <: u32)) =
  let _:Prims.unit = () <: Prims.unit in
  value &. ((1ul <<! n <: u32) -! 1ul <: u32)

let barrett_reduce (value: i32)
    : Prims.Pure i32
      (requires
        (Core.Convert.f_from value <: i64) >. (Core.Ops.Arith.Neg.neg v_BARRETT_R <: i64) &&
        (Core.Convert.f_from value <: i64) <. v_BARRETT_R)
      (ensures
        fun result ->
          let result:i32 = result in
          result >. (Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) &&
          result <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS) =
  let _:Prims.unit = () <: Prims.unit in
  let t:i64 =
    ((Core.Convert.f_from value <: i64) *! v_BARRETT_MULTIPLIER <: i64) +!
    (v_BARRETT_R >>! 1l <: i64)
  in
  let quotient:i32 = cast (t >>! v_BARRETT_SHIFT <: i64) <: i32 in
  let result:i32 = value -! (quotient *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) in
  let _:Prims.unit = () <: Prims.unit in
  result

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
  let _:i32 = v_MONTGOMERY_R in
  let _:Prims.unit = () <: Prims.unit in
  let t:u32 =
    (get_n_least_significant_bits v_MONTGOMERY_SHIFT (cast (value <: i32) <: u32) <: u32) *!
    v_INVERSE_OF_MODULUS_MOD_R
  in
  let k:i16 = cast (get_n_least_significant_bits v_MONTGOMERY_SHIFT t <: u32) <: i16 in
  let k_times_modulus:i32 =
    (cast (k <: i16) <: i32) *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
  in
  let c:i32 = k_times_modulus >>! v_MONTGOMERY_SHIFT in
  let value_high:i32 = value >>! v_MONTGOMERY_SHIFT in
  value_high -! c

let montgomery_multiply_sfe_by_fer (fe fer: i32) : i32 = montgomery_reduce (fe *! fer <: i32)

let to_standard_domain (mfe: i32) : i32 =
  montgomery_reduce (mfe *! v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS <: i32)

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

type t_PolynomialRingElement = { f_coefficients:t_Array i32 (sz 256) }

let impl__PolynomialRingElement__ZERO: t_PolynomialRingElement =
  { f_coefficients = Rust_primitives.Hax.repeat 0l (sz 256) } <: t_PolynomialRingElement

let add_to_ring_element (v_K: usize) (lhs rhs: t_PolynomialRingElement)
    : Prims.Pure t_PolynomialRingElement
      (requires
        Hax_lib.v_forall (fun i ->
              let i:usize = i in
              Hax_lib.implies (i <. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
                  <:
                  bool)
                (((Core.Num.impl__i32__abs (lhs.f_coefficients.[ i ] <: i32) <: i32) <=.
                    (((cast (v_K <: usize) <: i32) -! 1l <: i32) *!
                      Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                      <:
                      i32)
                    <:
                    bool) &&
                  ((Core.Num.impl__i32__abs (rhs.f_coefficients.[ i ] <: i32) <: i32) <=.
                    Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                    <:
                    bool))
              <:
              bool))
      (ensures
        fun result ->
          let result:t_PolynomialRingElement = result in
          Hax_lib.v_forall (fun i ->
                let i:usize = i in
                Hax_lib.implies (i <.
                    (Core.Slice.impl__len (Rust_primitives.unsize result.f_coefficients
                          <:
                          t_Slice i32)
                      <:
                      usize)
                    <:
                    bool)
                  ((Core.Num.impl__i32__abs (result.f_coefficients.[ i ] <: i32) <: i32) <=.
                    ((cast (v_K <: usize) <: i32) *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                      <:
                      i32)
                    <:
                    bool)
                <:
                bool)) =
  let _:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = () <: Prims.unit in
  let lhs:t_PolynomialRingElement =
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
          let lhs:t_PolynomialRingElement = lhs in
          let i:usize = i in
          {
            lhs with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs.f_coefficients
              i
              ((lhs.f_coefficients.[ i ] <: i32) +! (rhs.f_coefficients.[ i ] <: i32) <: i32)
            <:
            t_Array i32 (sz 256)
          }
          <:
          t_PolynomialRingElement)
  in
  let _:Prims.unit = () <: Prims.unit in
  lhs
