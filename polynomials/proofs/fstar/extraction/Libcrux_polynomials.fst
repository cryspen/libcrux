module Libcrux_polynomials
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Values having this type hold a representative 'x' of the Kyber field.
/// We use 'fe' as a shorthand for this type.
unfold
let t_FieldElement = i16

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R (mod FIELD_MODULUS).
/// We use 'fer' as a shorthand for this type.
unfold
let t_FieldElementTimesMontgomeryR = i16

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R^(-1) (mod FIELD_MODULUS).
/// We use 'mfe' as a shorthand for this type
unfold
let t_MontgomeryFieldElement = i16

/// This is calculated as ⌊(BARRETT_R / FIELD_MODULUS) + 1/2⌋
let v_BARRETT_MULTIPLIER: i32 = 20159l

let v_BARRETT_SHIFT: i32 = 26l

let v_BARRETT_R: i32 = 1l <<! v_BARRETT_SHIFT

let v_MONTGOMERY_SHIFT: u8 = 16uy

let v_MONTGOMERY_R: i32 = 1l <<! v_MONTGOMERY_SHIFT

/// The `compress_*` functions implement the `Compress` function specified in the NIST FIPS
/// 203 standard (Page 18, Expression 4.5), which is defined as:
/// ```plaintext
/// Compress_d: ℤq -> ℤ_{2ᵈ}
/// Compress_d(x) = ⌈(2ᵈ/q)·x⌋
/// ```
/// Since `⌈x⌋ = ⌊x + 1/2⌋` we have:
/// ```plaintext
/// Compress_d(x) = ⌊(2ᵈ/q)·x + 1/2⌋
///               = ⌊(2^{d+1}·x + q) / 2q⌋
/// ```
/// For further information about the function implementations, consult the
/// `implementation_notes.pdf` document in this directory.
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
let compress_message_coefficient (fe: u16) : u8 =
  let (shifted: i16):i16 = 1664s -! (cast (fe <: u16) <: i16) in
  let mask:i16 = shifted >>! 15l in
  let shifted_to_positive:i16 = mask ^. shifted in
  let shifted_positive_in_range:i16 = shifted_to_positive -! 832s in
  cast ((shifted_positive_in_range >>! 15l <: i16) &. 1s <: i16) <: u8

let get_n_least_significant_bits (n: u8) (value: u32)
    : Prims.Pure u32
      Prims.l_True
      (ensures
        fun result ->
          let result:u32 = result in
          result <. (Core.Num.impl__u32__pow 2ul (Core.Convert.f_into #u8 #u32 n <: u32) <: u32)) =
  value &. ((1ul <<! n <: u32) -! 1ul <: u32)

let compress_ciphertext_coefficient (coefficient_bits: u8) (fe: u16) : i16 =
  let compressed:u64 = (cast (fe <: u16) <: u64) <<! coefficient_bits in
  let compressed:u64 = compressed +! 1664uL in
  let compressed:u64 = compressed *! 10321340uL in
  let compressed:u64 = compressed >>! 35l in
  cast (get_n_least_significant_bits coefficient_bits (cast (compressed <: u64) <: u32) <: u32)
  <:
  i16

/// Signed Barrett Reduction
/// Given an input `value`, `barrett_reduce` outputs a representative `result`
/// such that:
/// - result ≡ value (mod FIELD_MODULUS)
/// - the absolute value of `result` is bound as follows:
/// `|result| ≤ FIELD_MODULUS / 2 · (|value|/BARRETT_R + 1)
/// In particular, if `|value| < BARRETT_R`, then `|result| < FIELD_MODULUS`.
let barrett_reduce_element (value: i16)
    : Prims.Pure i16
      (requires
        (Core.Convert.f_from #i32 #i16 value <: i32) >. (Core.Ops.Arith.Neg.neg v_BARRETT_R <: i32) &&
        (Core.Convert.f_from #i32 #i16 value <: i32) <. v_BARRETT_R)
      (ensures
        fun result ->
          let result:i16 = result in
          result >. (Core.Ops.Arith.Neg.neg Libcrux_traits.v_FIELD_MODULUS <: i16) &&
          result <. Libcrux_traits.v_FIELD_MODULUS) =
  let t:i32 =
    ((Core.Convert.f_from #i32 #i16 value <: i32) *! v_BARRETT_MULTIPLIER <: i32) +!
    (v_BARRETT_R >>! 1l <: i32)
  in
  let quotient:i16 = cast (t >>! v_BARRETT_SHIFT <: i32) <: i16 in
  value -! (quotient *! Libcrux_traits.v_FIELD_MODULUS <: i16)

/// Signed Montgomery Reduction
/// Given an input `value`, `montgomery_reduce` outputs a representative `o`
/// such that:
/// - o ≡ value · MONTGOMERY_R^(-1) (mod FIELD_MODULUS)
/// - the absolute value of `o` is bound as follows:
/// `|result| ≤ (|value| / MONTGOMERY_R) + (FIELD_MODULUS / 2)
/// In particular, if `|value| ≤ FIELD_MODULUS * MONTGOMERY_R`, then `|o| < (3 · FIELD_MODULUS) / 2`.
let montgomery_reduce_element (value: i32) : i16 =
  let _:i32 = v_MONTGOMERY_R in
  let k:i32 =
    (cast (cast (value <: i32) <: i16) <: i32) *!
    (cast (Libcrux_traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R <: u32) <: i32)
  in
  let k_times_modulus:i32 =
    (cast (cast (k <: i32) <: i16) <: i32) *! (cast (Libcrux_traits.v_FIELD_MODULUS <: i16) <: i32)
  in
  let c:i16 = cast (k_times_modulus >>! v_MONTGOMERY_SHIFT <: i32) <: i16 in
  let value_high:i16 = cast (value >>! v_MONTGOMERY_SHIFT <: i32) <: i16 in
  value_high -! c

/// If `fe` is some field element 'x' of the Kyber field and `fer` is congruent to
/// `y · MONTGOMERY_R`, this procedure outputs a value that is congruent to
/// `x · y`, as follows:
///    `fe · fer ≡ x · y · MONTGOMERY_R (mod FIELD_MODULUS)`
/// `montgomery_reduce` takes the value `x · y · MONTGOMERY_R` and outputs a representative
/// `x · y · MONTGOMERY_R * MONTGOMERY_R^{-1} ≡ x · y (mod FIELD_MODULUS)`.
let montgomery_multiply_fe_by_fer (fe fer: i16) : i16 =
  montgomery_reduce_element ((cast (fe <: i16) <: i32) *! (cast (fer <: i16) <: i32) <: i32)

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
let ntt_multiply_binomials (a0, a1: (i16 & i16)) (b0, b1: (i16 & i16)) (zeta: i16) : (i16 & i16) =
  montgomery_reduce_element (((cast (a0 <: i16) <: i32) *! (cast (b0 <: i16) <: i32) <: i32) +!
      ((cast (montgomery_reduce_element ((cast (a1 <: i16) <: i32) *! (cast (b1 <: i16) <: i32)
                  <:
                  i32)
              <:
              i16)
          <:
          i32) *!
        (cast (zeta <: i16) <: i32)
        <:
        i32)
      <:
      i32),
  montgomery_reduce_element (((cast (a0 <: i16) <: i32) *! (cast (b1 <: i16) <: i32) <: i32) +!
      ((cast (a1 <: i16) <: i32) *! (cast (b0 <: i16) <: i32) <: i32)
      <:
      i32)
  <:
  (i16 & i16)

let rej_sample (a: t_Slice u8) (result: t_Slice i16) : (t_Slice i16 & usize) =
  let sampled:usize = sz 0 in
  let result, sampled:(t_Slice i16 & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Chunks
            u8)
          (Core.Slice.impl__chunks #u8 a (sz 3) <: Core.Slice.Iter.t_Chunks u8)
        <:
        Core.Slice.Iter.t_Chunks u8)
      (result, sampled <: (t_Slice i16 & usize))
      (fun temp_0_ bytes ->
          let result, sampled:(t_Slice i16 & usize) = temp_0_ in
          let bytes:t_Slice u8 = bytes in
          let b1:i16 = cast (bytes.[ sz 0 ] <: u8) <: i16 in
          let b2:i16 = cast (bytes.[ sz 1 ] <: u8) <: i16 in
          let b3:i16 = cast (bytes.[ sz 2 ] <: u8) <: i16 in
          let d1:i16 = ((b2 &. 15s <: i16) <<! 8l <: i16) |. b1 in
          let d2:i16 = (b3 <<! 4l <: i16) |. (b2 >>! 4l <: i16) in
          let result, sampled:(t_Slice i16 & usize) =
            if d1 <. Libcrux_traits.v_FIELD_MODULUS && sampled <. sz 16
            then
              let result:t_Slice i16 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result sampled d1
              in
              result, sampled +! sz 1 <: (t_Slice i16 & usize)
            else result, sampled <: (t_Slice i16 & usize)
          in
          if d2 <. Libcrux_traits.v_FIELD_MODULUS && sampled <. sz 16
          then
            let result:t_Slice i16 =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result sampled d2
            in
            result, sampled +! sz 1 <: (t_Slice i16 & usize)
          else result, sampled <: (t_Slice i16 & usize))
  in
  let hax_temp_output:usize = sampled in
  result, hax_temp_output <: (t_Slice i16 & usize)

type t_PortableVector = { f_elements:t_Array i16 (sz 16) }

let add (lhs rhs: t_PortableVector) : t_PortableVector =
  let lhs:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      lhs
      (fun lhs i ->
          let lhs:t_PortableVector = lhs in
          let i:usize = i in
          {
            lhs with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs.f_elements
              i
              ((lhs.f_elements.[ i ] <: i16) +! (rhs.f_elements.[ i ] <: i16) <: i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          t_PortableVector)
  in
  lhs

let barrett_reduce (v: t_PortableVector) : t_PortableVector =
  let v:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:t_PortableVector = v in
          let i:usize = i in
          {
            v with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
              i
              (barrett_reduce_element (v.f_elements.[ i ] <: i16) <: i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          t_PortableVector)
  in
  v

let bitwise_and_with_constant (v: t_PortableVector) (c: i16) : t_PortableVector =
  let v:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:t_PortableVector = v in
          let i:usize = i in
          {
            v with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
              i
              ((v.f_elements.[ i ] <: i16) &. c <: i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          t_PortableVector)
  in
  v

let compress (v_COEFFICIENT_BITS: i32) (v: t_PortableVector) : t_PortableVector =
  let v:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:t_PortableVector = v in
          let i:usize = i in
          {
            v with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
              i
              (compress_ciphertext_coefficient (cast (v_COEFFICIENT_BITS <: i32) <: u8)
                  (cast (v.f_elements.[ i ] <: i16) <: u16)
                <:
                i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          t_PortableVector)
  in
  v

let compress_1_ (v: t_PortableVector) : t_PortableVector =
  let v:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:t_PortableVector = v in
          let i:usize = i in
          {
            v with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
              i
              (cast (compress_message_coefficient (cast (v.f_elements.[ i ] <: i16) <: u16) <: u8)
                <:
                i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          t_PortableVector)
  in
  v

let cond_subtract_3329_ (v: t_PortableVector) : t_PortableVector =
  let v:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:t_PortableVector = v in
          let i:usize = i in
          let _:Prims.unit =
            if true
            then
              let _:Prims.unit =
                if
                  ~.(((v.f_elements.[ i ] <: i16) >=. 0s <: bool) &&
                    ((v.f_elements.[ i ] <: i16) <. 4096s <: bool))
                then
                  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: v.elements[i] >= 0 && v.elements[i] < 4096"

                      <:
                      Rust_primitives.Hax.t_Never)
              in
              ()
          in
          if (v.f_elements.[ i ] <: i16) >=. 3329s
          then
            {
              v with
              f_elements
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
                i
                ((v.f_elements.[ i ] <: i16) -! 3329s <: i16)
            }
            <:
            t_PortableVector
          else v)
  in
  v

let from_i16_array (array: t_Slice i16) : t_PortableVector =
  {
    f_elements
    =
    Core.Result.impl__unwrap #(t_Array i16 (sz 16))
      #Core.Array.t_TryFromSliceError
      (Core.Convert.f_try_into #(t_Slice i16)
          #(t_Array i16 (sz 16))
          (array.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 16 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice i16)
        <:
        Core.Result.t_Result (t_Array i16 (sz 16)) Core.Array.t_TryFromSliceError)
  }
  <:
  t_PortableVector

let inv_ntt_layer_1_step (v: t_PortableVector) (zeta0 zeta1 zeta2 zeta3: i16) : t_PortableVector =
  let a_minus_b:i16 = (v.f_elements.[ sz 2 ] <: i16) -! (v.f_elements.[ sz 0 ] <: i16) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 0)
        (barrett_reduce_element ((v.f_elements.[ sz 0 ] <: i16) +! (v.f_elements.[ sz 2 ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 2)
        (montgomery_multiply_fe_by_fer a_minus_b zeta0 <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 = (v.f_elements.[ sz 3 ] <: i16) -! (v.f_elements.[ sz 1 ] <: i16) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 1)
        (barrett_reduce_element ((v.f_elements.[ sz 1 ] <: i16) +! (v.f_elements.[ sz 3 ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 3)
        (montgomery_multiply_fe_by_fer a_minus_b zeta0 <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 = (v.f_elements.[ sz 6 ] <: i16) -! (v.f_elements.[ sz 4 ] <: i16) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 4)
        (barrett_reduce_element ((v.f_elements.[ sz 4 ] <: i16) +! (v.f_elements.[ sz 6 ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 6)
        (montgomery_multiply_fe_by_fer a_minus_b zeta1 <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 = (v.f_elements.[ sz 7 ] <: i16) -! (v.f_elements.[ sz 5 ] <: i16) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 5)
        (barrett_reduce_element ((v.f_elements.[ sz 5 ] <: i16) +! (v.f_elements.[ sz 7 ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 7)
        (montgomery_multiply_fe_by_fer a_minus_b zeta1 <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 =
    (v.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) -!
    (v.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16)
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 0 <: usize)
        (barrett_reduce_element ((v.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) +!
              (v.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 2 <: usize)
        (montgomery_multiply_fe_by_fer a_minus_b zeta2 <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 =
    (v.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) -!
    (v.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16)
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 1 <: usize)
        (barrett_reduce_element ((v.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) +!
              (v.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 3 <: usize)
        (montgomery_multiply_fe_by_fer a_minus_b zeta2 <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 =
    (v.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) -!
    (v.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16)
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 4 <: usize)
        (barrett_reduce_element ((v.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) +!
              (v.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 6 <: usize)
        (montgomery_multiply_fe_by_fer a_minus_b zeta3 <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 =
    (v.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) -!
    (v.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16)
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 5 <: usize)
        (barrett_reduce_element ((v.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) +!
              (v.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 7 <: usize)
        (montgomery_multiply_fe_by_fer a_minus_b zeta3 <: i16)
    }
    <:
    t_PortableVector
  in
  v

let inv_ntt_layer_2_step (v: t_PortableVector) (zeta0 zeta1: i16) : t_PortableVector =
  let a_minus_b:i16 = (v.f_elements.[ sz 4 ] <: i16) -! (v.f_elements.[ sz 0 ] <: i16) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 0)
        ((v.f_elements.[ sz 0 ] <: i16) +! (v.f_elements.[ sz 4 ] <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 4)
        (montgomery_multiply_fe_by_fer a_minus_b zeta0 <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 = (v.f_elements.[ sz 5 ] <: i16) -! (v.f_elements.[ sz 1 ] <: i16) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 1)
        ((v.f_elements.[ sz 1 ] <: i16) +! (v.f_elements.[ sz 5 ] <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 5)
        (montgomery_multiply_fe_by_fer a_minus_b zeta0 <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 = (v.f_elements.[ sz 6 ] <: i16) -! (v.f_elements.[ sz 2 ] <: i16) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 2)
        ((v.f_elements.[ sz 2 ] <: i16) +! (v.f_elements.[ sz 6 ] <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 6)
        (montgomery_multiply_fe_by_fer a_minus_b zeta0 <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 = (v.f_elements.[ sz 7 ] <: i16) -! (v.f_elements.[ sz 3 ] <: i16) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 3)
        ((v.f_elements.[ sz 3 ] <: i16) +! (v.f_elements.[ sz 7 ] <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 7)
        (montgomery_multiply_fe_by_fer a_minus_b zeta0 <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 =
    (v.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) -!
    (v.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16)
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 0 <: usize)
        ((v.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) +!
          (v.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 4 <: usize)
        (montgomery_multiply_fe_by_fer a_minus_b zeta1 <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 =
    (v.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) -!
    (v.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16)
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 1 <: usize)
        ((v.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) +!
          (v.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 5 <: usize)
        (montgomery_multiply_fe_by_fer a_minus_b zeta1 <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 =
    (v.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) -!
    (v.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16)
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 2 <: usize)
        ((v.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) +!
          (v.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 6 <: usize)
        (montgomery_multiply_fe_by_fer a_minus_b zeta1 <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 =
    (v.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) -!
    (v.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16)
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 3 <: usize)
        ((v.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) +!
          (v.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 7 <: usize)
        (montgomery_multiply_fe_by_fer a_minus_b zeta1 <: i16)
    }
    <:
    t_PortableVector
  in
  v

let inv_ntt_layer_3_step (v: t_PortableVector) (zeta: i16) : t_PortableVector =
  let a_minus_b:i16 = (v.f_elements.[ sz 8 ] <: i16) -! (v.f_elements.[ sz 0 ] <: i16) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 0)
        ((v.f_elements.[ sz 0 ] <: i16) +! (v.f_elements.[ sz 8 ] <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8)
        (montgomery_multiply_fe_by_fer a_minus_b zeta <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 = (v.f_elements.[ sz 9 ] <: i16) -! (v.f_elements.[ sz 1 ] <: i16) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 1)
        ((v.f_elements.[ sz 1 ] <: i16) +! (v.f_elements.[ sz 9 ] <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 9)
        (montgomery_multiply_fe_by_fer a_minus_b zeta <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 = (v.f_elements.[ sz 10 ] <: i16) -! (v.f_elements.[ sz 2 ] <: i16) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 2)
        ((v.f_elements.[ sz 2 ] <: i16) +! (v.f_elements.[ sz 10 ] <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 10)
        (montgomery_multiply_fe_by_fer a_minus_b zeta <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 = (v.f_elements.[ sz 11 ] <: i16) -! (v.f_elements.[ sz 3 ] <: i16) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 3)
        ((v.f_elements.[ sz 3 ] <: i16) +! (v.f_elements.[ sz 11 ] <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 11)
        (montgomery_multiply_fe_by_fer a_minus_b zeta <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 = (v.f_elements.[ sz 12 ] <: i16) -! (v.f_elements.[ sz 4 ] <: i16) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 4)
        ((v.f_elements.[ sz 4 ] <: i16) +! (v.f_elements.[ sz 12 ] <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 12)
        (montgomery_multiply_fe_by_fer a_minus_b zeta <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 = (v.f_elements.[ sz 13 ] <: i16) -! (v.f_elements.[ sz 5 ] <: i16) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 5)
        ((v.f_elements.[ sz 5 ] <: i16) +! (v.f_elements.[ sz 13 ] <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 13)
        (montgomery_multiply_fe_by_fer a_minus_b zeta <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 = (v.f_elements.[ sz 14 ] <: i16) -! (v.f_elements.[ sz 6 ] <: i16) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 6)
        ((v.f_elements.[ sz 6 ] <: i16) +! (v.f_elements.[ sz 14 ] <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 14)
        (montgomery_multiply_fe_by_fer a_minus_b zeta <: i16)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i16 = (v.f_elements.[ sz 15 ] <: i16) -! (v.f_elements.[ sz 7 ] <: i16) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 7)
        ((v.f_elements.[ sz 7 ] <: i16) +! (v.f_elements.[ sz 15 ] <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 15)
        (montgomery_multiply_fe_by_fer a_minus_b zeta <: i16)
    }
    <:
    t_PortableVector
  in
  v

let montgomery_multiply_by_constant (v: t_PortableVector) (c: i16) : t_PortableVector =
  let v:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:t_PortableVector = v in
          let i:usize = i in
          {
            v with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
              i
              (montgomery_multiply_fe_by_fer (v.f_elements.[ i ] <: i16) c <: i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          t_PortableVector)
  in
  v

let multiply_by_constant (v: t_PortableVector) (c: i16) : t_PortableVector =
  let v:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:t_PortableVector = v in
          let i:usize = i in
          {
            v with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
              i
              ((v.f_elements.[ i ] <: i16) *! c <: i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          t_PortableVector)
  in
  v

let ntt_layer_1_step (v: t_PortableVector) (zeta0 zeta1 zeta2 zeta3: i16) : t_PortableVector =
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 2 ] <: i16) zeta0 in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 2)
        ((v.f_elements.[ sz 0 ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 0)
        ((v.f_elements.[ sz 0 ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 3 ] <: i16) zeta0 in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 3)
        ((v.f_elements.[ sz 1 ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 1)
        ((v.f_elements.[ sz 1 ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 6 ] <: i16) zeta1 in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 6)
        ((v.f_elements.[ sz 4 ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 4)
        ((v.f_elements.[ sz 4 ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 7 ] <: i16) zeta1 in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 7)
        ((v.f_elements.[ sz 5 ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 5)
        ((v.f_elements.[ sz 5 ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) zeta2 in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 2 <: usize)
        ((v.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 0 <: usize)
        ((v.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) zeta2 in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 3 <: usize)
        ((v.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 1 <: usize)
        ((v.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) zeta3 in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 6 <: usize)
        ((v.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 4 <: usize)
        ((v.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) zeta3 in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 7 <: usize)
        ((v.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 5 <: usize)
        ((v.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  v

let ntt_layer_2_step (v: t_PortableVector) (zeta0 zeta1: i16) : t_PortableVector =
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 4 ] <: i16) zeta0 in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 4)
        ((v.f_elements.[ sz 0 ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 0)
        ((v.f_elements.[ sz 0 ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 5 ] <: i16) zeta0 in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 5)
        ((v.f_elements.[ sz 1 ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 1)
        ((v.f_elements.[ sz 1 ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 6 ] <: i16) zeta0 in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 6)
        ((v.f_elements.[ sz 2 ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 2)
        ((v.f_elements.[ sz 2 ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 7 ] <: i16) zeta0 in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 7)
        ((v.f_elements.[ sz 3 ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 3)
        ((v.f_elements.[ sz 3 ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) zeta1 in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 4 <: usize)
        ((v.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 0 <: usize)
        ((v.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) zeta1 in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 5 <: usize)
        ((v.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 1 <: usize)
        ((v.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) zeta1 in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 6 <: usize)
        ((v.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 2 <: usize)
        ((v.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) zeta1 in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 7 <: usize)
        ((v.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8 +! sz 3 <: usize)
        ((v.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  v

let ntt_layer_3_step (v: t_PortableVector) (zeta: i16) : t_PortableVector =
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 8 ] <: i16) zeta in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8)
        ((v.f_elements.[ sz 0 ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 0)
        ((v.f_elements.[ sz 0 ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 9 ] <: i16) zeta in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 9)
        ((v.f_elements.[ sz 1 ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 1)
        ((v.f_elements.[ sz 1 ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 10 ] <: i16) zeta in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 10)
        ((v.f_elements.[ sz 2 ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 2)
        ((v.f_elements.[ sz 2 ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 11 ] <: i16) zeta in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 11)
        ((v.f_elements.[ sz 3 ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 3)
        ((v.f_elements.[ sz 3 ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 12 ] <: i16) zeta in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 12)
        ((v.f_elements.[ sz 4 ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 4)
        ((v.f_elements.[ sz 4 ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 13 ] <: i16) zeta in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 13)
        ((v.f_elements.[ sz 5 ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 5)
        ((v.f_elements.[ sz 5 ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 14 ] <: i16) zeta in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 14)
        ((v.f_elements.[ sz 6 ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 6)
        ((v.f_elements.[ sz 6 ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  let t:i16 = montgomery_multiply_fe_by_fer (v.f_elements.[ sz 15 ] <: i16) zeta in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 15)
        ((v.f_elements.[ sz 7 ] <: i16) -! t <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 7)
        ((v.f_elements.[ sz 7 ] <: i16) +! t <: i16)
    }
    <:
    t_PortableVector
  in
  v

let serialize_1_ (v: t_PortableVector) : t_Array u8 (sz 2) =
  let result:t_Array u8 (sz 2) = Rust_primitives.Hax.repeat 0uy (sz 2) in
  let result:t_Array u8 (sz 2) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      result
      (fun result i ->
          let result:t_Array u8 (sz 2) = result in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
            (sz 0)
            ((result.[ sz 0 ] <: u8) |. ((cast (v.f_elements.[ i ] <: i16) <: u8) <<! i <: u8) <: u8
            )
          <:
          t_Array u8 (sz 2))
  in
  let result:t_Array u8 (sz 2) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 8; Core.Ops.Range.f_end = sz 16 }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      result
      (fun result i ->
          let result:t_Array u8 (sz 2) = result in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
            (sz 1)
            ((result.[ sz 1 ] <: u8) |.
              ((cast (v.f_elements.[ i ] <: i16) <: u8) <<! (i -! sz 8 <: usize) <: u8)
              <:
              u8)
          <:
          t_Array u8 (sz 2))
  in
  result

let serialize_10_ (v: t_PortableVector) : t_Array u8 (sz 20) =
  let result:t_Array u8 (sz 20) = Rust_primitives.Hax.repeat 0uy (sz 20) in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast ((v.f_elements.[ sz 0 ] <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (((cast ((v.f_elements.[ sz 1 ] <: i16) &. 63s <: i16) <: u8) <<! 2l <: u8) |.
        (cast (((v.f_elements.[ sz 0 ] <: i16) >>! 8l <: i16) &. 3s <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (((cast ((v.f_elements.[ sz 2 ] <: i16) &. 15s <: i16) <: u8) <<! 4l <: u8) |.
        (cast (((v.f_elements.[ sz 1 ] <: i16) >>! 6l <: i16) &. 15s <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (((cast ((v.f_elements.[ sz 3 ] <: i16) &. 3s <: i16) <: u8) <<! 6l <: u8) |.
        (cast (((v.f_elements.[ sz 2 ] <: i16) >>! 4l <: i16) &. 63s <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (cast (((v.f_elements.[ sz 3 ] <: i16) >>! 2l <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (cast ((v.f_elements.[ sz 4 ] <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (((cast ((v.f_elements.[ sz 5 ] <: i16) &. 63s <: i16) <: u8) <<! 2l <: u8) |.
        (cast (((v.f_elements.[ sz 4 ] <: i16) >>! 8l <: i16) &. 3s <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (((cast ((v.f_elements.[ sz 6 ] <: i16) &. 15s <: i16) <: u8) <<! 4l <: u8) |.
        (cast (((v.f_elements.[ sz 5 ] <: i16) >>! 6l <: i16) &. 15s <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 8)
      (((cast ((v.f_elements.[ sz 7 ] <: i16) &. 3s <: i16) <: u8) <<! 6l <: u8) |.
        (cast (((v.f_elements.[ sz 6 ] <: i16) >>! 4l <: i16) &. 63s <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 9)
      (cast (((v.f_elements.[ sz 7 ] <: i16) >>! 2l <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 10)
      (cast ((v.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11)
      (((cast ((v.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) &. 63s <: i16) <: u8) <<! 2l <: u8) |.
        (cast (((v.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) >>! 8l <: i16) &. 3s <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 12)
      (((cast ((v.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) &. 15s <: i16) <: u8) <<! 4l <: u8) |.
        (cast (((v.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) >>! 6l <: i16) &. 15s <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 13)
      (((cast ((v.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) &. 3s <: i16) <: u8) <<! 6l <: u8) |.
        (cast (((v.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) >>! 4l <: i16) &. 63s <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 14)
      (cast (((v.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) >>! 2l <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 15)
      (cast ((v.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 16)
      (((cast ((v.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) &. 63s <: i16) <: u8) <<! 2l <: u8) |.
        (cast (((v.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) >>! 8l <: i16) &. 3s <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 17)
      (((cast ((v.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) &. 15s <: i16) <: u8) <<! 4l <: u8) |.
        (cast (((v.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) >>! 6l <: i16) &. 15s <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 18)
      (((cast ((v.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) &. 3s <: i16) <: u8) <<! 6l <: u8) |.
        (cast (((v.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) >>! 4l <: i16) &. 63s <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 19)
      (cast (((v.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) >>! 2l <: i16) &. 255s <: i16) <: u8)
  in
  result

let serialize_11_ (v: t_PortableVector) : t_Array u8 (sz 22) =
  let result:t_Array u8 (sz 22) = Rust_primitives.Hax.repeat 0uy (sz 22) in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast (v.f_elements.[ sz 0 ] <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (((cast ((v.f_elements.[ sz 1 ] <: i16) &. 31s <: i16) <: u8) <<! 3l <: u8) |.
        (cast ((v.f_elements.[ sz 0 ] <: i16) >>! 8l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (((cast ((v.f_elements.[ sz 2 ] <: i16) &. 3s <: i16) <: u8) <<! 6l <: u8) |.
        (cast ((v.f_elements.[ sz 1 ] <: i16) >>! 5l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (cast (((v.f_elements.[ sz 2 ] <: i16) >>! 2l <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (((cast ((v.f_elements.[ sz 3 ] <: i16) &. 127s <: i16) <: u8) <<! 1l <: u8) |.
        (cast ((v.f_elements.[ sz 2 ] <: i16) >>! 10l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (((cast ((v.f_elements.[ sz 4 ] <: i16) &. 15s <: i16) <: u8) <<! 4l <: u8) |.
        (cast ((v.f_elements.[ sz 3 ] <: i16) >>! 7l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (((cast ((v.f_elements.[ sz 5 ] <: i16) &. 1s <: i16) <: u8) <<! 7l <: u8) |.
        (cast ((v.f_elements.[ sz 4 ] <: i16) >>! 4l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (cast (((v.f_elements.[ sz 5 ] <: i16) >>! 1l <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 8)
      (((cast ((v.f_elements.[ sz 6 ] <: i16) &. 63s <: i16) <: u8) <<! 2l <: u8) |.
        (cast ((v.f_elements.[ sz 5 ] <: i16) >>! 9l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 9)
      (((cast ((v.f_elements.[ sz 7 ] <: i16) &. 7s <: i16) <: u8) <<! 5l <: u8) |.
        (cast ((v.f_elements.[ sz 6 ] <: i16) >>! 6l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 10)
      (cast ((v.f_elements.[ sz 7 ] <: i16) >>! 3l <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11)
      (cast (v.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 12)
      (((cast ((v.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) &. 31s <: i16) <: u8) <<! 3l <: u8) |.
        (cast ((v.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) >>! 8l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 13)
      (((cast ((v.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) &. 3s <: i16) <: u8) <<! 6l <: u8) |.
        (cast ((v.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) >>! 5l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 14)
      (cast (((v.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) >>! 2l <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 15)
      (((cast ((v.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) &. 127s <: i16) <: u8) <<! 1l <: u8) |.
        (cast ((v.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) >>! 10l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 16)
      (((cast ((v.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) &. 15s <: i16) <: u8) <<! 4l <: u8) |.
        (cast ((v.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) >>! 7l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 17)
      (((cast ((v.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) &. 1s <: i16) <: u8) <<! 7l <: u8) |.
        (cast ((v.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) >>! 4l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 18)
      (cast (((v.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) >>! 1l <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 19)
      (((cast ((v.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) &. 63s <: i16) <: u8) <<! 2l <: u8) |.
        (cast ((v.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) >>! 9l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 20)
      (((cast ((v.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) &. 7s <: i16) <: u8) <<! 5l <: u8) |.
        (cast ((v.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) >>! 6l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 21)
      (cast ((v.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) >>! 3l <: i16) <: u8)
  in
  result

let serialize_12_ (v: t_PortableVector) : t_Array u8 (sz 24) =
  let result:t_Array u8 (sz 24) = Rust_primitives.Hax.repeat 0uy (sz 24) in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast ((v.f_elements.[ sz 0 ] <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (cast (((v.f_elements.[ sz 0 ] <: i16) >>! 8l <: i16) |.
            (((v.f_elements.[ sz 1 ] <: i16) &. 15s <: i16) <<! 4l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (cast (((v.f_elements.[ sz 1 ] <: i16) >>! 4l <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (cast ((v.f_elements.[ sz 2 ] <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (cast (((v.f_elements.[ sz 2 ] <: i16) >>! 8l <: i16) |.
            (((v.f_elements.[ sz 3 ] <: i16) &. 15s <: i16) <<! 4l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (cast (((v.f_elements.[ sz 3 ] <: i16) >>! 4l <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (cast ((v.f_elements.[ sz 4 ] <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (cast (((v.f_elements.[ sz 4 ] <: i16) >>! 8l <: i16) |.
            (((v.f_elements.[ sz 5 ] <: i16) &. 15s <: i16) <<! 4l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 8)
      (cast (((v.f_elements.[ sz 5 ] <: i16) >>! 4l <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 9)
      (cast ((v.f_elements.[ sz 6 ] <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 10)
      (cast (((v.f_elements.[ sz 6 ] <: i16) >>! 8l <: i16) |.
            (((v.f_elements.[ sz 7 ] <: i16) &. 15s <: i16) <<! 4l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11)
      (cast (((v.f_elements.[ sz 7 ] <: i16) >>! 4l <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 12)
      (cast ((v.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 13)
      (cast (((v.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) >>! 8l <: i16) |.
            (((v.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) &. 15s <: i16) <<! 4l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 14)
      (cast (((v.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) >>! 4l <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 15)
      (cast ((v.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 16)
      (cast (((v.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) >>! 8l <: i16) |.
            (((v.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) &. 15s <: i16) <<! 4l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 17)
      (cast (((v.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) >>! 4l <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 18)
      (cast ((v.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 19)
      (cast (((v.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) >>! 8l <: i16) |.
            (((v.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) &. 15s <: i16) <<! 4l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 20)
      (cast (((v.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) >>! 4l <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 21)
      (cast ((v.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 22)
      (cast (((v.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) >>! 8l <: i16) |.
            (((v.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) &. 15s <: i16) <<! 4l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 23)
      (cast (((v.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) >>! 4l <: i16) &. 255s <: i16) <: u8)
  in
  result

let serialize_4_ (v: t_PortableVector) : t_Array u8 (sz 8) =
  let result:t_Array u8 (sz 8) = Rust_primitives.Hax.repeat 0uy (sz 8) in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (((cast (v.f_elements.[ sz 1 ] <: i16) <: u8) <<! 4l <: u8) |.
        (cast (v.f_elements.[ sz 0 ] <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (((cast (v.f_elements.[ sz 3 ] <: i16) <: u8) <<! 4l <: u8) |.
        (cast (v.f_elements.[ sz 2 ] <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (((cast (v.f_elements.[ sz 5 ] <: i16) <: u8) <<! 4l <: u8) |.
        (cast (v.f_elements.[ sz 4 ] <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (((cast (v.f_elements.[ sz 7 ] <: i16) <: u8) <<! 4l <: u8) |.
        (cast (v.f_elements.[ sz 6 ] <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (((cast (v.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) <: u8) <<! 4l <: u8) |.
        (cast (v.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (((cast (v.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) <: u8) <<! 4l <: u8) |.
        (cast (v.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (((cast (v.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) <: u8) <<! 4l <: u8) |.
        (cast (v.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (((cast (v.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) <: u8) <<! 4l <: u8) |.
        (cast (v.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) <: u8)
        <:
        u8)
  in
  result

let serialize_5_ (v: t_PortableVector) : t_Array u8 (sz 10) =
  let result:t_Array u8 (sz 10) = Rust_primitives.Hax.repeat 0uy (sz 10) in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast ((((v.f_elements.[ sz 1 ] <: i16) &. 7s <: i16) <<! 5l <: i16) |.
            (v.f_elements.[ sz 0 ] <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (cast (((((v.f_elements.[ sz 3 ] <: i16) &. 1s <: i16) <<! 7l <: i16) |.
              ((v.f_elements.[ sz 2 ] <: i16) <<! 2l <: i16)
              <:
              i16) |.
            ((v.f_elements.[ sz 1 ] <: i16) >>! 3l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (cast ((((v.f_elements.[ sz 4 ] <: i16) &. 15s <: i16) <<! 4l <: i16) |.
            ((v.f_elements.[ sz 3 ] <: i16) >>! 1l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (cast (((((v.f_elements.[ sz 6 ] <: i16) &. 3s <: i16) <<! 6l <: i16) |.
              ((v.f_elements.[ sz 5 ] <: i16) <<! 1l <: i16)
              <:
              i16) |.
            ((v.f_elements.[ sz 4 ] <: i16) >>! 4l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (cast (((v.f_elements.[ sz 7 ] <: i16) <<! 3l <: i16) |.
            ((v.f_elements.[ sz 6 ] <: i16) >>! 2l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (cast ((((v.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) &. 7s <: i16) <<! 5l <: i16) |.
            (v.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (cast (((((v.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) &. 1s <: i16) <<! 7l <: i16) |.
              ((v.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) <<! 2l <: i16)
              <:
              i16) |.
            ((v.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) >>! 3l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (cast ((((v.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) &. 15s <: i16) <<! 4l <: i16) |.
            ((v.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) >>! 1l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 8)
      (cast (((((v.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) &. 3s <: i16) <<! 6l <: i16) |.
              ((v.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) <<! 1l <: i16)
              <:
              i16) |.
            ((v.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) >>! 4l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 9)
      (cast (((v.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) <<! 3l <: i16) |.
            ((v.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) >>! 2l <: i16)
            <:
            i16)
        <:
        u8)
  in
  result

let shift_left (v_SHIFT_BY: i32) (lhs: t_PortableVector) : t_PortableVector =
  let lhs:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      lhs
      (fun lhs i ->
          let lhs:t_PortableVector = lhs in
          let i:usize = i in
          {
            lhs with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs.f_elements
              i
              ((lhs.f_elements.[ i ] <: i16) <<! v_SHIFT_BY <: i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          t_PortableVector)
  in
  lhs

let shift_right (v_SHIFT_BY: i32) (v: t_PortableVector) : t_PortableVector =
  let v:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:t_PortableVector = v in
          let i:usize = i in
          {
            v with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
              i
              ((v.f_elements.[ i ] <: i16) >>! v_SHIFT_BY <: i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          t_PortableVector)
  in
  v

let sub (lhs rhs: t_PortableVector) : t_PortableVector =
  let lhs:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      lhs
      (fun lhs i ->
          let lhs:t_PortableVector = lhs in
          let i:usize = i in
          {
            lhs with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs.f_elements
              i
              ((lhs.f_elements.[ i ] <: i16) -! (rhs.f_elements.[ i ] <: i16) <: i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          t_PortableVector)
  in
  lhs

let to_i16_array (v: t_PortableVector) : t_Array i16 (sz 16) = v.f_elements

let decompress_ciphertext_coefficient (v_COEFFICIENT_BITS: i32) (v: t_PortableVector)
    : t_PortableVector =
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i16 (sz 16) & bool) =
        Core.Iter.Traits.Iterator.f_all #(Core.Array.Iter.t_IntoIter i16 (sz 16))
          (Core.Iter.Traits.Collect.f_into_iter #(t_Array i16 (sz 16))
              (to_i16_array v <: t_Array i16 (sz 16))
            <:
            Core.Array.Iter.t_IntoIter i16 (sz 16))
          (fun coefficient ->
              let coefficient:i16 = coefficient in
              (Core.Num.impl__i16__abs coefficient <: i16) <. (1s <<! v_COEFFICIENT_BITS <: i16)
              <:
              bool)
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: to_i16_array(v).into_iter().all(|coefficient|\\n        coefficient.abs() < 1 << COEFFICIENT_BITS)"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let v:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:t_PortableVector = v in
          let i:usize = i in
          let decompressed:i32 =
            (cast (v.f_elements.[ i ] <: i16) <: i32) *!
            (cast (Libcrux_traits.v_FIELD_MODULUS <: i16) <: i32)
          in
          let decompressed:i32 =
            (decompressed <<! 1l <: i32) +! (1l <<! v_COEFFICIENT_BITS <: i32)
          in
          let decompressed:i32 = decompressed >>! (v_COEFFICIENT_BITS +! 1l <: i32) in
          let v:t_PortableVector =
            {
              v with
              f_elements
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
                i
                (cast (decompressed <: i32) <: i16)
            }
            <:
            t_PortableVector
          in
          v)
  in
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i16 (sz 16) & bool) =
        Core.Iter.Traits.Iterator.f_all #(Core.Array.Iter.t_IntoIter i16 (sz 16))
          (Core.Iter.Traits.Collect.f_into_iter #(t_Array i16 (sz 16))
              (to_i16_array v <: t_Array i16 (sz 16))
            <:
            Core.Array.Iter.t_IntoIter i16 (sz 16))
          (fun coefficient ->
              let coefficient:i16 = coefficient in
              (cast (Core.Num.impl__i16__abs coefficient <: i16) <: u16) <=. (1us <<! 12l <: u16)
              <:
              bool)
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: to_i16_array(v).into_iter().all(|coefficient|\\n        coefficient.abs() as u16 <= 1 << 12)"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  v

let zero (_: Prims.unit) : t_PortableVector =
  { f_elements = Rust_primitives.Hax.repeat 0s (sz 16) } <: t_PortableVector

let deserialize_1_ (v: t_Slice u8) : t_PortableVector =
  let result:t_PortableVector = zero () in
  let result:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      result
      (fun result i ->
          let result:t_PortableVector = result in
          let i:usize = i in
          {
            result with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
              i
              (cast (((v.[ sz 0 ] <: u8) >>! i <: u8) &. 1uy <: u8) <: i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          t_PortableVector)
  in
  let result:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 8;
              Core.Ops.Range.f_end = Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      result
      (fun result i ->
          let result:t_PortableVector = result in
          let i:usize = i in
          {
            result with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
              i
              (cast (((v.[ sz 1 ] <: u8) >>! (i -! sz 8 <: usize) <: u8) &. 1uy <: u8) <: i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          t_PortableVector)
  in
  result

let deserialize_10_ (bytes: t_Slice u8) : t_PortableVector =
  let result:t_PortableVector = zero () in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 0)
        ((((cast (bytes.[ sz 1 ] <: u8) <: i16) &. 3s <: i16) <<! 8l <: i16) |.
          ((cast (bytes.[ sz 0 ] <: u8) <: i16) &. 255s <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 1)
        ((((cast (bytes.[ sz 2 ] <: u8) <: i16) &. 15s <: i16) <<! 6l <: i16) |.
          ((cast (bytes.[ sz 1 ] <: u8) <: i16) >>! 2l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 2)
        ((((cast (bytes.[ sz 3 ] <: u8) <: i16) &. 63s <: i16) <<! 4l <: i16) |.
          ((cast (bytes.[ sz 2 ] <: u8) <: i16) >>! 4l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 3)
        (((cast (bytes.[ sz 4 ] <: u8) <: i16) <<! 2l <: i16) |.
          ((cast (bytes.[ sz 3 ] <: u8) <: i16) >>! 6l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 4)
        ((((cast (bytes.[ sz 6 ] <: u8) <: i16) &. 3s <: i16) <<! 8l <: i16) |.
          ((cast (bytes.[ sz 5 ] <: u8) <: i16) &. 255s <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 5)
        ((((cast (bytes.[ sz 7 ] <: u8) <: i16) &. 15s <: i16) <<! 6l <: i16) |.
          ((cast (bytes.[ sz 6 ] <: u8) <: i16) >>! 2l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 6)
        ((((cast (bytes.[ sz 8 ] <: u8) <: i16) &. 63s <: i16) <<! 4l <: i16) |.
          ((cast (bytes.[ sz 7 ] <: u8) <: i16) >>! 4l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 7)
        (((cast (bytes.[ sz 9 ] <: u8) <: i16) <<! 2l <: i16) |.
          ((cast (bytes.[ sz 8 ] <: u8) <: i16) >>! 6l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 8)
        ((((cast (bytes.[ sz 10 +! sz 1 <: usize ] <: u8) <: i16) &. 3s <: i16) <<! 8l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 0 <: usize ] <: u8) <: i16) &. 255s <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 9)
        ((((cast (bytes.[ sz 10 +! sz 2 <: usize ] <: u8) <: i16) &. 15s <: i16) <<! 6l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 1 <: usize ] <: u8) <: i16) >>! 2l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 10)
        ((((cast (bytes.[ sz 10 +! sz 3 <: usize ] <: u8) <: i16) &. 63s <: i16) <<! 4l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 2 <: usize ] <: u8) <: i16) >>! 4l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 11)
        (((cast (bytes.[ sz 10 +! sz 4 <: usize ] <: u8) <: i16) <<! 2l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 3 <: usize ] <: u8) <: i16) >>! 6l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 12)
        ((((cast (bytes.[ sz 10 +! sz 6 <: usize ] <: u8) <: i16) &. 3s <: i16) <<! 8l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 5 <: usize ] <: u8) <: i16) &. 255s <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 13)
        ((((cast (bytes.[ sz 10 +! sz 7 <: usize ] <: u8) <: i16) &. 15s <: i16) <<! 6l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 6 <: usize ] <: u8) <: i16) >>! 2l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 14)
        ((((cast (bytes.[ sz 10 +! sz 8 <: usize ] <: u8) <: i16) &. 63s <: i16) <<! 4l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 7 <: usize ] <: u8) <: i16) >>! 4l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 15)
        (((cast (bytes.[ sz 10 +! sz 9 <: usize ] <: u8) <: i16) <<! 2l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 8 <: usize ] <: u8) <: i16) >>! 6l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  result

let deserialize_11_ (bytes: t_Slice u8) : t_PortableVector =
  let result:t_PortableVector = zero () in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 0)
        ((((cast (bytes.[ sz 1 ] <: u8) <: i16) &. 7s <: i16) <<! 8l <: i16) |.
          (cast (bytes.[ sz 0 ] <: u8) <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 1)
        ((((cast (bytes.[ sz 2 ] <: u8) <: i16) &. 63s <: i16) <<! 5l <: i16) |.
          ((cast (bytes.[ sz 1 ] <: u8) <: i16) >>! 3l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 2)
        (((((cast (bytes.[ sz 4 ] <: u8) <: i16) &. 1s <: i16) <<! 10l <: i16) |.
            ((cast (bytes.[ sz 3 ] <: u8) <: i16) <<! 2l <: i16)
            <:
            i16) |.
          ((cast (bytes.[ sz 2 ] <: u8) <: i16) >>! 6l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 3)
        ((((cast (bytes.[ sz 5 ] <: u8) <: i16) &. 15s <: i16) <<! 7l <: i16) |.
          ((cast (bytes.[ sz 4 ] <: u8) <: i16) >>! 1l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 4)
        ((((cast (bytes.[ sz 6 ] <: u8) <: i16) &. 127s <: i16) <<! 4l <: i16) |.
          ((cast (bytes.[ sz 5 ] <: u8) <: i16) >>! 4l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 5)
        (((((cast (bytes.[ sz 8 ] <: u8) <: i16) &. 3s <: i16) <<! 9l <: i16) |.
            ((cast (bytes.[ sz 7 ] <: u8) <: i16) <<! 1l <: i16)
            <:
            i16) |.
          ((cast (bytes.[ sz 6 ] <: u8) <: i16) >>! 7l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 6)
        ((((cast (bytes.[ sz 9 ] <: u8) <: i16) &. 31s <: i16) <<! 6l <: i16) |.
          ((cast (bytes.[ sz 8 ] <: u8) <: i16) >>! 2l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 7)
        (((cast (bytes.[ sz 10 ] <: u8) <: i16) <<! 3l <: i16) |.
          ((cast (bytes.[ sz 9 ] <: u8) <: i16) >>! 5l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 8)
        ((((cast (bytes.[ sz 11 +! sz 1 <: usize ] <: u8) <: i16) &. 7s <: i16) <<! 8l <: i16) |.
          (cast (bytes.[ sz 11 +! sz 0 <: usize ] <: u8) <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 9)
        ((((cast (bytes.[ sz 11 +! sz 2 <: usize ] <: u8) <: i16) &. 63s <: i16) <<! 5l <: i16) |.
          ((cast (bytes.[ sz 11 +! sz 1 <: usize ] <: u8) <: i16) >>! 3l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 10)
        (((((cast (bytes.[ sz 11 +! sz 4 <: usize ] <: u8) <: i16) &. 1s <: i16) <<! 10l <: i16) |.
            ((cast (bytes.[ sz 11 +! sz 3 <: usize ] <: u8) <: i16) <<! 2l <: i16)
            <:
            i16) |.
          ((cast (bytes.[ sz 11 +! sz 2 <: usize ] <: u8) <: i16) >>! 6l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 11)
        ((((cast (bytes.[ sz 11 +! sz 5 <: usize ] <: u8) <: i16) &. 15s <: i16) <<! 7l <: i16) |.
          ((cast (bytes.[ sz 11 +! sz 4 <: usize ] <: u8) <: i16) >>! 1l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 12)
        ((((cast (bytes.[ sz 11 +! sz 6 <: usize ] <: u8) <: i16) &. 127s <: i16) <<! 4l <: i16) |.
          ((cast (bytes.[ sz 11 +! sz 5 <: usize ] <: u8) <: i16) >>! 4l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 13)
        (((((cast (bytes.[ sz 11 +! sz 8 <: usize ] <: u8) <: i16) &. 3s <: i16) <<! 9l <: i16) |.
            ((cast (bytes.[ sz 11 +! sz 7 <: usize ] <: u8) <: i16) <<! 1l <: i16)
            <:
            i16) |.
          ((cast (bytes.[ sz 11 +! sz 6 <: usize ] <: u8) <: i16) >>! 7l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 14)
        ((((cast (bytes.[ sz 11 +! sz 9 <: usize ] <: u8) <: i16) &. 31s <: i16) <<! 6l <: i16) |.
          ((cast (bytes.[ sz 11 +! sz 8 <: usize ] <: u8) <: i16) >>! 2l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 15)
        (((cast (bytes.[ sz 11 +! sz 10 <: usize ] <: u8) <: i16) <<! 3l <: i16) |.
          ((cast (bytes.[ sz 11 +! sz 9 <: usize ] <: u8) <: i16) >>! 5l <: i16)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  result

let deserialize_12_ (bytes: t_Slice u8) : t_PortableVector =
  let re:t_PortableVector = zero () in
  let byte0:i16 = cast (bytes.[ sz 0 ] <: u8) <: i16 in
  let byte1:i16 = cast (bytes.[ sz 1 ] <: u8) <: i16 in
  let byte2:i16 = cast (bytes.[ sz 2 ] <: u8) <: i16 in
  let byte3:i16 = cast (bytes.[ sz 3 ] <: u8) <: i16 in
  let byte4:i16 = cast (bytes.[ sz 4 ] <: u8) <: i16 in
  let byte5:i16 = cast (bytes.[ sz 5 ] <: u8) <: i16 in
  let byte6:i16 = cast (bytes.[ sz 6 ] <: u8) <: i16 in
  let byte7:i16 = cast (bytes.[ sz 7 ] <: u8) <: i16 in
  let byte8:i16 = cast (bytes.[ sz 8 ] <: u8) <: i16 in
  let byte9:i16 = cast (bytes.[ sz 9 ] <: u8) <: i16 in
  let byte10:i16 = cast (bytes.[ sz 10 ] <: u8) <: i16 in
  let byte11:i16 = cast (bytes.[ sz 11 ] <: u8) <: i16 in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 0)
        (((byte1 &. 15s <: i16) <<! 8l <: i16) |. (byte0 &. 255s <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 1)
        ((byte2 <<! 4l <: i16) |. ((byte1 >>! 4l <: i16) &. 15s <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 2)
        (((byte4 &. 15s <: i16) <<! 8l <: i16) |. (byte3 &. 255s <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 3)
        ((byte5 <<! 4l <: i16) |. ((byte4 >>! 4l <: i16) &. 15s <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 4)
        (((byte7 &. 15s <: i16) <<! 8l <: i16) |. (byte6 &. 255s <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 5)
        ((byte8 <<! 4l <: i16) |. ((byte7 >>! 4l <: i16) &. 15s <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 6)
        (((byte10 &. 15s <: i16) <<! 8l <: i16) |. (byte9 &. 255s <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 7)
        ((byte11 <<! 4l <: i16) |. ((byte10 >>! 4l <: i16) &. 15s <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let byte12:i16 = cast (bytes.[ sz 12 ] <: u8) <: i16 in
  let byte13:i16 = cast (bytes.[ sz 13 ] <: u8) <: i16 in
  let byte14:i16 = cast (bytes.[ sz 14 ] <: u8) <: i16 in
  let byte15:i16 = cast (bytes.[ sz 15 ] <: u8) <: i16 in
  let byte16:i16 = cast (bytes.[ sz 16 ] <: u8) <: i16 in
  let byte17:i16 = cast (bytes.[ sz 17 ] <: u8) <: i16 in
  let byte18:i16 = cast (bytes.[ sz 18 ] <: u8) <: i16 in
  let byte19:i16 = cast (bytes.[ sz 19 ] <: u8) <: i16 in
  let byte20:i16 = cast (bytes.[ sz 20 ] <: u8) <: i16 in
  let byte21:i16 = cast (bytes.[ sz 21 ] <: u8) <: i16 in
  let byte22:i16 = cast (bytes.[ sz 22 ] <: u8) <: i16 in
  let byte23:i16 = cast (bytes.[ sz 23 ] <: u8) <: i16 in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 8)
        (((byte13 &. 15s <: i16) <<! 8l <: i16) |. (byte12 &. 255s <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 9)
        ((byte14 <<! 4l <: i16) |. ((byte13 >>! 4l <: i16) &. 15s <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 10)
        (((byte16 &. 15s <: i16) <<! 8l <: i16) |. (byte15 &. 255s <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 11)
        ((byte17 <<! 4l <: i16) |. ((byte16 >>! 4l <: i16) &. 15s <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 12)
        (((byte19 &. 15s <: i16) <<! 8l <: i16) |. (byte18 &. 255s <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 13)
        ((byte20 <<! 4l <: i16) |. ((byte19 >>! 4l <: i16) &. 15s <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 14)
        (((byte22 &. 15s <: i16) <<! 8l <: i16) |. (byte21 &. 255s <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 15)
        ((byte23 <<! 4l <: i16) |. ((byte22 >>! 4l <: i16) &. 15s <: i16) <: i16)
    }
    <:
    t_PortableVector
  in
  re

let deserialize_4_ (bytes: t_Slice u8) : t_PortableVector =
  let v:t_PortableVector = zero () in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 0)
        (cast ((bytes.[ sz 0 ] <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 1)
        (cast (((bytes.[ sz 0 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 2)
        (cast ((bytes.[ sz 1 ] <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 3)
        (cast (((bytes.[ sz 1 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 4)
        (cast ((bytes.[ sz 2 ] <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 5)
        (cast (((bytes.[ sz 2 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 6)
        (cast ((bytes.[ sz 3 ] <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 7)
        (cast (((bytes.[ sz 3 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8)
        (cast ((bytes.[ sz 4 ] <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 9)
        (cast (((bytes.[ sz 4 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 10)
        (cast ((bytes.[ sz 5 ] <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 11)
        (cast (((bytes.[ sz 5 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 12)
        (cast ((bytes.[ sz 6 ] <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 13)
        (cast (((bytes.[ sz 6 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 14)
        (cast ((bytes.[ sz 7 ] <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 15)
        (cast (((bytes.[ sz 7 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  v

let deserialize_5_ (bytes: t_Slice u8) : t_PortableVector =
  let v:t_PortableVector = zero () in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 0)
        (cast ((bytes.[ sz 0 ] <: u8) &. 31uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 1)
        (cast ((((bytes.[ sz 1 ] <: u8) &. 3uy <: u8) <<! 3l <: u8) |.
              ((bytes.[ sz 0 ] <: u8) >>! 5l <: u8)
              <:
              u8)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 2)
        (cast (((bytes.[ sz 1 ] <: u8) >>! 2l <: u8) &. 31uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 3)
        (cast ((((bytes.[ sz 2 ] <: u8) &. 15uy <: u8) <<! 1l <: u8) |.
              ((bytes.[ sz 1 ] <: u8) >>! 7l <: u8)
              <:
              u8)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 4)
        (cast ((((bytes.[ sz 3 ] <: u8) &. 1uy <: u8) <<! 4l <: u8) |.
              ((bytes.[ sz 2 ] <: u8) >>! 4l <: u8)
              <:
              u8)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 5)
        (cast (((bytes.[ sz 3 ] <: u8) >>! 1l <: u8) &. 31uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 6)
        (cast ((((bytes.[ sz 4 ] <: u8) &. 7uy <: u8) <<! 2l <: u8) |.
              ((bytes.[ sz 3 ] <: u8) >>! 6l <: u8)
              <:
              u8)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 7)
        (cast ((bytes.[ sz 4 ] <: u8) >>! 3l <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 8)
        (cast ((bytes.[ sz 5 +! sz 0 <: usize ] <: u8) &. 31uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 9)
        (cast ((((bytes.[ sz 5 +! sz 1 <: usize ] <: u8) &. 3uy <: u8) <<! 3l <: u8) |.
              ((bytes.[ sz 5 +! sz 0 <: usize ] <: u8) >>! 5l <: u8)
              <:
              u8)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 10)
        (cast (((bytes.[ sz 5 +! sz 1 <: usize ] <: u8) >>! 2l <: u8) &. 31uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 11)
        (cast ((((bytes.[ sz 5 +! sz 2 <: usize ] <: u8) &. 15uy <: u8) <<! 1l <: u8) |.
              ((bytes.[ sz 5 +! sz 1 <: usize ] <: u8) >>! 7l <: u8)
              <:
              u8)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 12)
        (cast ((((bytes.[ sz 5 +! sz 3 <: usize ] <: u8) &. 1uy <: u8) <<! 4l <: u8) |.
              ((bytes.[ sz 5 +! sz 2 <: usize ] <: u8) >>! 4l <: u8)
              <:
              u8)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 13)
        (cast (((bytes.[ sz 5 +! sz 3 <: usize ] <: u8) >>! 1l <: u8) &. 31uy <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 14)
        (cast ((((bytes.[ sz 5 +! sz 4 <: usize ] <: u8) &. 7uy <: u8) <<! 2l <: u8) |.
              ((bytes.[ sz 5 +! sz 3 <: usize ] <: u8) >>! 6l <: u8)
              <:
              u8)
          <:
          i16)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 15)
        (cast ((bytes.[ sz 5 +! sz 4 <: usize ] <: u8) >>! 3l <: u8) <: i16)
    }
    <:
    t_PortableVector
  in
  v

let ntt_multiply (lhs rhs: t_PortableVector) (zeta0 zeta1 zeta2 zeta3: i16) : t_PortableVector =
  let out:t_PortableVector = zero () in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.f_elements.[ sz 0 ] <: i16), (lhs.f_elements.[ sz 1 ] <: i16)
        <:
        (i16 & i16))
      ((rhs.f_elements.[ sz 0 ] <: i16), (rhs.f_elements.[ sz 1 ] <: i16) <: (i16 & i16))
      zeta0
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 0) product._1
    }
    <:
    t_PortableVector
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 1) product._2
    }
    <:
    t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.f_elements.[ sz 2 ] <: i16), (lhs.f_elements.[ sz 3 ] <: i16)
        <:
        (i16 & i16))
      ((rhs.f_elements.[ sz 2 ] <: i16), (rhs.f_elements.[ sz 3 ] <: i16) <: (i16 & i16))
      (Core.Ops.Arith.Neg.neg zeta0 <: i16)
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 2) product._1
    }
    <:
    t_PortableVector
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 3) product._2
    }
    <:
    t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.f_elements.[ sz 4 ] <: i16), (lhs.f_elements.[ sz 5 ] <: i16)
        <:
        (i16 & i16))
      ((rhs.f_elements.[ sz 4 ] <: i16), (rhs.f_elements.[ sz 5 ] <: i16) <: (i16 & i16))
      zeta1
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 4) product._1
    }
    <:
    t_PortableVector
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 5) product._2
    }
    <:
    t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.f_elements.[ sz 6 ] <: i16), (lhs.f_elements.[ sz 7 ] <: i16)
        <:
        (i16 & i16))
      ((rhs.f_elements.[ sz 6 ] <: i16), (rhs.f_elements.[ sz 7 ] <: i16) <: (i16 & i16))
      (Core.Ops.Arith.Neg.neg zeta1 <: i16)
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 6) product._1
    }
    <:
    t_PortableVector
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 7) product._2
    }
    <:
    t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16),
        (lhs.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16)
        <:
        (i16 & i16))
      ((rhs.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16),
        (rhs.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16)
        <:
        (i16 & i16))
      zeta2
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements
        (sz 8 +! sz 0 <: usize)
        product._1
    }
    <:
    t_PortableVector
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements
        (sz 8 +! sz 1 <: usize)
        product._2
    }
    <:
    t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16),
        (lhs.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16)
        <:
        (i16 & i16))
      ((rhs.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16),
        (rhs.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16)
        <:
        (i16 & i16))
      (Core.Ops.Arith.Neg.neg zeta2 <: i16)
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements
        (sz 8 +! sz 2 <: usize)
        product._1
    }
    <:
    t_PortableVector
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements
        (sz 8 +! sz 3 <: usize)
        product._2
    }
    <:
    t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16),
        (lhs.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16)
        <:
        (i16 & i16))
      ((rhs.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16),
        (rhs.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16)
        <:
        (i16 & i16))
      zeta3
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements
        (sz 8 +! sz 4 <: usize)
        product._1
    }
    <:
    t_PortableVector
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements
        (sz 8 +! sz 5 <: usize)
        product._2
    }
    <:
    t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16),
        (lhs.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16)
        <:
        (i16 & i16))
      ((rhs.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16),
        (rhs.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16)
        <:
        (i16 & i16))
      (Core.Ops.Arith.Neg.neg zeta3 <: i16)
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements
        (sz 8 +! sz 6 <: usize)
        product._1
    }
    <:
    t_PortableVector
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements
        (sz 8 +! sz 7 <: usize)
        product._2
    }
    <:
    t_PortableVector
  in
  out

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_traits.t_Operations t_PortableVector =
  {
    _super_14285531652857523276 = FStar.Tactics.Typeclasses.solve;
    _super_10391689928755043351 = FStar.Tactics.Typeclasses.solve;
    f_ZERO_pre = (fun (_: Prims.unit) -> true);
    f_ZERO_post = (fun (_: Prims.unit) (out: t_PortableVector) -> true);
    f_ZERO = (fun (_: Prims.unit) -> zero ());
    f_to_i16_array_pre = (fun (v: t_PortableVector) -> true);
    f_to_i16_array_post = (fun (v: t_PortableVector) (out: t_Array i16 (sz 16)) -> true);
    f_to_i16_array = (fun (v: t_PortableVector) -> to_i16_array v);
    f_from_i16_array_pre = (fun (array: t_Slice i16) -> true);
    f_from_i16_array_post = (fun (array: t_Slice i16) (out: t_PortableVector) -> true);
    f_from_i16_array = (fun (array: t_Slice i16) -> from_i16_array array);
    f_add_pre = (fun (lhs: t_PortableVector) (rhs: t_PortableVector) -> true);
    f_add_post
    =
    (fun (lhs: t_PortableVector) (rhs: t_PortableVector) (out: t_PortableVector) -> true);
    f_add = (fun (lhs: t_PortableVector) (rhs: t_PortableVector) -> add lhs rhs);
    f_sub_pre = (fun (lhs: t_PortableVector) (rhs: t_PortableVector) -> true);
    f_sub_post
    =
    (fun (lhs: t_PortableVector) (rhs: t_PortableVector) (out: t_PortableVector) -> true);
    f_sub = (fun (lhs: t_PortableVector) (rhs: t_PortableVector) -> sub lhs rhs);
    f_multiply_by_constant_pre = (fun (v: t_PortableVector) (c: i16) -> true);
    f_multiply_by_constant_post
    =
    (fun (v: t_PortableVector) (c: i16) (out: t_PortableVector) -> true);
    f_multiply_by_constant = (fun (v: t_PortableVector) (c: i16) -> multiply_by_constant v c);
    f_bitwise_and_with_constant_pre = (fun (v: t_PortableVector) (c: i16) -> true);
    f_bitwise_and_with_constant_post
    =
    (fun (v: t_PortableVector) (c: i16) (out: t_PortableVector) -> true);
    f_bitwise_and_with_constant
    =
    (fun (v: t_PortableVector) (c: i16) -> bitwise_and_with_constant v c);
    f_shift_right_pre = (fun (v_SHIFT_BY: i32) (v: t_PortableVector) -> true);
    f_shift_right_post
    =
    (fun (v_SHIFT_BY: i32) (v: t_PortableVector) (out: t_PortableVector) -> true);
    f_shift_right = (fun (v_SHIFT_BY: i32) (v: t_PortableVector) -> shift_right v_SHIFT_BY v);
    f_shift_left_pre = (fun (v_SHIFT_BY: i32) (v: t_PortableVector) -> true);
    f_shift_left_post
    =
    (fun (v_SHIFT_BY: i32) (v: t_PortableVector) (out: t_PortableVector) -> true);
    f_shift_left = (fun (v_SHIFT_BY: i32) (v: t_PortableVector) -> shift_left v_SHIFT_BY v);
    f_cond_subtract_3329_pre = (fun (v: t_PortableVector) -> true);
    f_cond_subtract_3329_post = (fun (v: t_PortableVector) (out: t_PortableVector) -> true);
    f_cond_subtract_3329_ = (fun (v: t_PortableVector) -> cond_subtract_3329_ v);
    f_barrett_reduce_pre = (fun (v: t_PortableVector) -> true);
    f_barrett_reduce_post = (fun (v: t_PortableVector) (out: t_PortableVector) -> true);
    f_barrett_reduce = (fun (v: t_PortableVector) -> barrett_reduce v);
    f_montgomery_multiply_by_constant_pre = (fun (v: t_PortableVector) (r: i16) -> true);
    f_montgomery_multiply_by_constant_post
    =
    (fun (v: t_PortableVector) (r: i16) (out: t_PortableVector) -> true);
    f_montgomery_multiply_by_constant
    =
    (fun (v: t_PortableVector) (r: i16) -> montgomery_multiply_by_constant v r);
    f_compress_1_pre = (fun (v: t_PortableVector) -> true);
    f_compress_1_post = (fun (v: t_PortableVector) (out: t_PortableVector) -> true);
    f_compress_1_ = (fun (v: t_PortableVector) -> compress_1_ v);
    f_compress_pre = (fun (v_COEFFICIENT_BITS: i32) (v: t_PortableVector) -> true);
    f_compress_post
    =
    (fun (v_COEFFICIENT_BITS: i32) (v: t_PortableVector) (out: t_PortableVector) -> true);
    f_compress
    =
    (fun (v_COEFFICIENT_BITS: i32) (v: t_PortableVector) -> compress v_COEFFICIENT_BITS v);
    f_decompress_ciphertext_coefficient_pre
    =
    (fun (v_COEFFICIENT_BITS: i32) (v: t_PortableVector) -> true);
    f_decompress_ciphertext_coefficient_post
    =
    (fun (v_COEFFICIENT_BITS: i32) (v: t_PortableVector) (out: t_PortableVector) -> true);
    f_decompress_ciphertext_coefficient
    =
    (fun (v_COEFFICIENT_BITS: i32) (v: t_PortableVector) ->
        decompress_ciphertext_coefficient v_COEFFICIENT_BITS v);
    f_ntt_layer_1_step_pre
    =
    (fun (a: t_PortableVector) (zeta0: i16) (zeta1: i16) (zeta2: i16) (zeta3: i16) -> true);
    f_ntt_layer_1_step_post
    =
    (fun
        (a: t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (out: t_PortableVector)
        ->
        true);
    f_ntt_layer_1_step
    =
    (fun (a: t_PortableVector) (zeta0: i16) (zeta1: i16) (zeta2: i16) (zeta3: i16) ->
        ntt_layer_1_step a zeta0 zeta1 zeta2 zeta3);
    f_ntt_layer_2_step_pre = (fun (a: t_PortableVector) (zeta0: i16) (zeta1: i16) -> true);
    f_ntt_layer_2_step_post
    =
    (fun (a: t_PortableVector) (zeta0: i16) (zeta1: i16) (out: t_PortableVector) -> true);
    f_ntt_layer_2_step
    =
    (fun (a: t_PortableVector) (zeta0: i16) (zeta1: i16) -> ntt_layer_2_step a zeta0 zeta1);
    f_ntt_layer_3_step_pre = (fun (a: t_PortableVector) (zeta: i16) -> true);
    f_ntt_layer_3_step_post
    =
    (fun (a: t_PortableVector) (zeta: i16) (out: t_PortableVector) -> true);
    f_ntt_layer_3_step = (fun (a: t_PortableVector) (zeta: i16) -> ntt_layer_3_step a zeta);
    f_inv_ntt_layer_1_step_pre
    =
    (fun (a: t_PortableVector) (zeta0: i16) (zeta1: i16) (zeta2: i16) (zeta3: i16) -> true);
    f_inv_ntt_layer_1_step_post
    =
    (fun
        (a: t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (out: t_PortableVector)
        ->
        true);
    f_inv_ntt_layer_1_step
    =
    (fun (a: t_PortableVector) (zeta0: i16) (zeta1: i16) (zeta2: i16) (zeta3: i16) ->
        inv_ntt_layer_1_step a zeta0 zeta1 zeta2 zeta3);
    f_inv_ntt_layer_2_step_pre = (fun (a: t_PortableVector) (zeta0: i16) (zeta1: i16) -> true);
    f_inv_ntt_layer_2_step_post
    =
    (fun (a: t_PortableVector) (zeta0: i16) (zeta1: i16) (out: t_PortableVector) -> true);
    f_inv_ntt_layer_2_step
    =
    (fun (a: t_PortableVector) (zeta0: i16) (zeta1: i16) -> inv_ntt_layer_2_step a zeta0 zeta1);
    f_inv_ntt_layer_3_step_pre = (fun (a: t_PortableVector) (zeta: i16) -> true);
    f_inv_ntt_layer_3_step_post
    =
    (fun (a: t_PortableVector) (zeta: i16) (out: t_PortableVector) -> true);
    f_inv_ntt_layer_3_step = (fun (a: t_PortableVector) (zeta: i16) -> inv_ntt_layer_3_step a zeta);
    f_ntt_multiply_pre
    =
    (fun
        (lhs: t_PortableVector)
        (rhs: t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        true);
    f_ntt_multiply_post
    =
    (fun
        (lhs: t_PortableVector)
        (rhs: t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (out: t_PortableVector)
        ->
        true);
    f_ntt_multiply
    =
    (fun
        (lhs: t_PortableVector)
        (rhs: t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        ntt_multiply lhs rhs zeta0 zeta1 zeta2 zeta3);
    f_serialize_1_pre = (fun (a: t_PortableVector) -> true);
    f_serialize_1_post = (fun (a: t_PortableVector) (out: t_Array u8 (sz 2)) -> true);
    f_serialize_1_ = (fun (a: t_PortableVector) -> serialize_1_ a);
    f_deserialize_1_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_1_post = (fun (a: t_Slice u8) (out: t_PortableVector) -> true);
    f_deserialize_1_ = (fun (a: t_Slice u8) -> deserialize_1_ a);
    f_serialize_4_pre = (fun (a: t_PortableVector) -> true);
    f_serialize_4_post = (fun (a: t_PortableVector) (out: t_Array u8 (sz 8)) -> true);
    f_serialize_4_ = (fun (a: t_PortableVector) -> serialize_4_ a);
    f_deserialize_4_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_4_post = (fun (a: t_Slice u8) (out: t_PortableVector) -> true);
    f_deserialize_4_ = (fun (a: t_Slice u8) -> deserialize_4_ a);
    f_serialize_5_pre = (fun (a: t_PortableVector) -> true);
    f_serialize_5_post = (fun (a: t_PortableVector) (out: t_Array u8 (sz 10)) -> true);
    f_serialize_5_ = (fun (a: t_PortableVector) -> serialize_5_ a);
    f_deserialize_5_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_5_post = (fun (a: t_Slice u8) (out: t_PortableVector) -> true);
    f_deserialize_5_ = (fun (a: t_Slice u8) -> deserialize_5_ a);
    f_serialize_10_pre = (fun (a: t_PortableVector) -> true);
    f_serialize_10_post = (fun (a: t_PortableVector) (out: t_Array u8 (sz 20)) -> true);
    f_serialize_10_ = (fun (a: t_PortableVector) -> serialize_10_ a);
    f_deserialize_10_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_10_post = (fun (a: t_Slice u8) (out: t_PortableVector) -> true);
    f_deserialize_10_ = (fun (a: t_Slice u8) -> deserialize_10_ a);
    f_serialize_11_pre = (fun (a: t_PortableVector) -> true);
    f_serialize_11_post = (fun (a: t_PortableVector) (out: t_Array u8 (sz 22)) -> true);
    f_serialize_11_ = (fun (a: t_PortableVector) -> serialize_11_ a);
    f_deserialize_11_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_11_post = (fun (a: t_Slice u8) (out: t_PortableVector) -> true);
    f_deserialize_11_ = (fun (a: t_Slice u8) -> deserialize_11_ a);
    f_serialize_12_pre = (fun (a: t_PortableVector) -> true);
    f_serialize_12_post = (fun (a: t_PortableVector) (out: t_Array u8 (sz 24)) -> true);
    f_serialize_12_ = (fun (a: t_PortableVector) -> serialize_12_ a);
    f_deserialize_12_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_12_post = (fun (a: t_Slice u8) (out: t_PortableVector) -> true);
    f_deserialize_12_ = (fun (a: t_Slice u8) -> deserialize_12_ a);
    f_rej_sample_pre = (fun (a: t_Slice u8) (out: t_Slice i16) -> true);
    f_rej_sample_post
    =
    (fun (a: t_Slice u8) (out: t_Slice i16) (out2: (t_Slice i16 & usize)) -> true);
    f_rej_sample
    =
    fun (a: t_Slice u8) (out: t_Slice i16) ->
      let tmp0, out1:(t_Slice i16 & usize) = rej_sample a out in
      let out:t_Slice i16 = tmp0 in
      let hax_temp_output:usize = out1 in
      out, hax_temp_output <: (t_Slice i16 & usize)
  }
