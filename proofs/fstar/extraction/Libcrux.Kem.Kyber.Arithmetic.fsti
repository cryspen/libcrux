module Libcrux.Kem.Kyber.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Values having this type hold a representative 'x' of the Kyber field.
/// We use 'fe' as a shorthand for this type.
unfold
let t_FieldElement = i32

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R (mod FIELD_MODULUS).
/// We use 'fer' as a shorthand for this type.
unfold
let t_FieldElementTimesMontgomeryR = i32

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R^(-1) (mod FIELD_MODULUS).
/// We use 'mfe' as a shorthand for this type
unfold
let t_MontgomeryFieldElement = i32

/// This is calculated as ⌊(BARRETT_R / FIELD_MODULUS) + 1/2⌋
let v_BARRETT_MULTIPLIER: i64 = 20159L

let v_BARRETT_SHIFT: i64 = 26L

let v_BARRETT_R: i64 = 1L <<! v_BARRETT_SHIFT

let v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u32 = 62209ul

/// This is calculated as (MONTGOMERY_R)^2 mod FIELD_MODULUS
let v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i32 = 1353l

let v_MONTGOMERY_SHIFT: u8 = 16uy

let v_MONTGOMERY_R: i32 = 1l <<! v_MONTGOMERY_SHIFT

val get_n_least_significant_bits (n: u8) (value: u32)
    : Prims.Pure u32
      (requires n =. 4uy || n =. 5uy || n =. 10uy || n =. 11uy || n =. v_MONTGOMERY_SHIFT)
      (ensures
        fun result ->
          let result:u32 = result in
          result <. (Core.Num.impl__u32__pow 2ul (Core.Convert.f_into #u8 #u32 n <: u32) <: u32))

/// Signed Barrett Reduction
/// Given an input `value`, `barrett_reduce` outputs a representative `result`
/// such that:
/// - result ≡ value (mod FIELD_MODULUS)
/// - the absolute value of `result` is bound as follows:
/// `|result| ≤ FIELD_MODULUS / 2 · (|value|/BARRETT_R + 1)
/// In particular, if `|value| < BARRETT_R`, then `|result| < FIELD_MODULUS`.
val barrett_reduce (value: i32)
    : Prims.Pure i32
      (requires
        (Core.Convert.f_from #i64 #i32 value <: i64) >. (Core.Ops.Arith.Neg.neg v_BARRETT_R <: i64) &&
        (Core.Convert.f_from #i64 #i32 value <: i64) <. v_BARRETT_R)
      (ensures
        fun result ->
          let result:i32 = result in
          result >. (Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) &&
          result <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS)

/// Signed Montgomery Reduction
/// Given an input `value`, `montgomery_reduce` outputs a representative `o`
/// such that:
/// - o ≡ value · MONTGOMERY_R^(-1) (mod FIELD_MODULUS)
/// - the absolute value of `o` is bound as follows:
/// `|result| ≤ (|value| / MONTGOMERY_R) + (FIELD_MODULUS / 2)
/// In particular, if `|value| ≤ FIELD_MODULUS * MONTGOMERY_R`, then `|o| < (3 · FIELD_MODULUS) / 2`.
val montgomery_reduce (value: i32)
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
          result <=. ((3l *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) /! 2l <: i32))

/// If `fe` is some field element 'x' of the Kyber field and `fer` is congruent to
/// `y · MONTGOMERY_R`, this procedure outputs a value that is congruent to
/// `x · y`, as follows:
///    `fe · fer ≡ x · y · MONTGOMERY_R (mod FIELD_MODULUS)`
/// `montgomery_reduce` takes the value `x · y · MONTGOMERY_R` and outputs a representative
/// `x · y · MONTGOMERY_R * MONTGOMERY_R^{-1} ≡ x · y (mod FIELD_MODULUS)`.
val montgomery_multiply_fe_by_fer (fe fer: i32)
    : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

/// If x is some field element of the Kyber field and `mfe` is congruent to
/// x · MONTGOMERY_R^{-1}, this procedure outputs a value that is congruent to
/// `x`, as follows:
///    mfe · MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS ≡ x · MONTGOMERY_R^{-1} * (MONTGOMERY_R)^2 (mod FIELD_MODULUS)
/// => mfe · MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS ≡ x · MONTGOMERY_R (mod FIELD_MODULUS)
/// `montgomery_reduce` takes the value `x · MONTGOMERY_R` and outputs a representative
/// `x · MONTGOMERY_R * MONTGOMERY_R^{-1} ≡ x (mod FIELD_MODULUS)`
val to_standard_domain (mfe: i32) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

/// Given a field element `fe` such that -FIELD_MODULUS ≤ fe < FIELD_MODULUS,
/// output `o` such that:
/// - `o` is congruent to `fe`
/// - 0 ≤ `o` FIELD_MODULUS
val to_unsigned_representative (fe: i32)
    : Prims.Pure u16
      (requires
        fe >=. (Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) &&
        fe <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS)
      (ensures
        fun result ->
          let result:u16 = result in
          result >=. 0us &&
          result <. (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u16))

type t_PolynomialRingElement = { f_coefficients:t_Array i32 (sz 256) }

let impl__PolynomialRingElement__ZERO: t_PolynomialRingElement =
  { f_coefficients = Rust_primitives.Hax.repeat 0l (sz 256) } <: t_PolynomialRingElement

/// Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
/// sum of their constituent coefficients.
val add_to_ring_element (v_K: usize) (lhs rhs: t_PolynomialRingElement)
    : Prims.Pure t_PolynomialRingElement
      (requires
        Hax_lib.v_forall #usize
          (fun i ->
              let i:usize = i in
              Hax_lib.implies (i <. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
                  <:
                  bool)
                (fun temp_0_ ->
                    let _:Prims.unit = temp_0_ in
                    ((Core.Num.impl__i32__abs (lhs.f_coefficients.[ i ] <: i32) <: i32) <=.
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
          Hax_lib.v_forall #usize
            (fun i ->
                let i:usize = i in
                Hax_lib.implies (i <.
                    (Core.Slice.impl__len #i32
                        (Rust_primitives.unsize result.f_coefficients <: t_Slice i32)
                      <:
                      usize)
                    <:
                    bool)
                  (fun temp_0_ ->
                      let _:Prims.unit = temp_0_ in
                      (Core.Num.impl__i32__abs (result.f_coefficients.[ i ] <: i32) <: i32) <=.
                      ((cast (v_K <: usize) <: i32) *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                        <:
                        i32)
                      <:
                      bool)
                <:
                bool))
