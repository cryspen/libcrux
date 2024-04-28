module Libcrux_ml_kem.Arithmetic
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
          result <. (Core.Num.impl__u32__pow 2ul (Core.Convert.f_into n <: u32) <: u32))

/// Given a field element `fe` such that -FIELD_MODULUS ≤ fe < FIELD_MODULUS,
/// output `o` such that:
/// - `o` is congruent to `fe`
/// - 0 ≤ `o` FIELD_MODULUS
val v__to_unsigned_representative (fe: i32)
    : Prims.Pure u16
      (requires
        fe >=. (Core.Ops.Arith.Neg.neg Libcrux_ml_kem.Constants.v_FIELD_MODULUS <: i32) &&
        fe <. Libcrux_ml_kem.Constants.v_FIELD_MODULUS)
      (ensures
        fun result ->
          let result:u16 = result in
          result >=. 0us &&
          result <. (cast (Libcrux_ml_kem.Constants.v_FIELD_MODULUS <: i32) <: u16))

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
        (Core.Convert.f_from value <: i64) >. (Core.Ops.Arith.Neg.neg v_BARRETT_R <: i64) &&
        (Core.Convert.f_from value <: i64) <. v_BARRETT_R)
      (ensures
        fun result ->
          let result:i32 = result in
          result >. (Core.Ops.Arith.Neg.neg Libcrux_ml_kem.Constants.v_FIELD_MODULUS <: i32) &&
          result <. Libcrux_ml_kem.Constants.v_FIELD_MODULUS)

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
        ((Core.Ops.Arith.Neg.neg Libcrux_ml_kem.Constants.v_FIELD_MODULUS <: i32) *! v_MONTGOMERY_R
          <:
          i32) &&
        value <=. (Libcrux_ml_kem.Constants.v_FIELD_MODULUS *! v_MONTGOMERY_R <: i32))
      (ensures
        fun result ->
          let result:i32 = result in
          result >=.
          ((Core.Ops.Arith.Neg.neg (3l *! Libcrux_ml_kem.Constants.v_FIELD_MODULUS <: i32) <: i32) /!
            2l
            <:
            i32) &&
          result <=. ((3l *! Libcrux_ml_kem.Constants.v_FIELD_MODULUS <: i32) /! 2l <: i32))

/// If x is some field element of the Kyber field and `mfe` is congruent to
/// x · MONTGOMERY_R^{-1}, this procedure outputs a value that is congruent to
/// `x`, as follows:
///    mfe · MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS ≡ x · MONTGOMERY_R^{-1} * (MONTGOMERY_R)^2 (mod FIELD_MODULUS)
/// => mfe · MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS ≡ x · MONTGOMERY_R (mod FIELD_MODULUS)
/// `montgomery_reduce` takes the value `x · MONTGOMERY_R` and outputs a representative
/// `x · MONTGOMERY_R * MONTGOMERY_R^{-1} ≡ x (mod FIELD_MODULUS)`
val v__to_standard_domain (mfe: i32) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

/// If `fe` is some field element 'x' of the Kyber field and `fer` is congruent to
/// `y · MONTGOMERY_R`, this procedure outputs a value that is congruent to
/// `x · y`, as follows:
///    `fe · fer ≡ x · y · MONTGOMERY_R (mod FIELD_MODULUS)`
/// `montgomery_reduce` takes the value `x · y · MONTGOMERY_R` and outputs a representative
/// `x · y · MONTGOMERY_R * MONTGOMERY_R^{-1} ≡ x · y (mod FIELD_MODULUS)`.
val montgomery_multiply_fe_by_fer (fe fer: i32)
    : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

/// Compute the product of two Kyber binomials with respect to the
/// modulus `X² - zeta`.
/// This function almost implements <strong>Algorithm 11</strong> of the
/// NIST FIPS 203 standard, which is reproduced below:
/// ```plaintext
/// Input:  a₀, a₁, b₀, b₁ ∈ ℤq.
/// Input: γ ∈ ℤq.
/// Output: c₀, c₁ ∈ ℤq.
/// c₀ ← a₀·b₀ + a₁·b₁·γ
/// c₁ ← a₀·b₁ + a₁·b₀
/// return c₀, c₁
/// ```
/// We say "almost" because the coefficients output by this function are in
/// the Montgomery domain (unlike in the specification).
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val ntt_multiply_binomials: (i32 & i32) -> (i32 & i32) -> zeta: i32
  -> Prims.Pure (i32 & i32) Prims.l_True (fun _ -> Prims.l_True)
