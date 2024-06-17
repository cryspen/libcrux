module Libcrux_ml_kem.Polynomial
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Traits in
  ()

let v_VECTORS_IN_RING_ELEMENT: usize = Rust_primitives.Hax.dropped_body

let v_ZETAS_TIMES_MONTGOMERY_R: t_Array i16 (sz 128) = Rust_primitives.Hax.dropped_body

type t_PolynomialRingElement
  (v_Vector: Type0) {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = { f_coefficients:t_Array v_Vector (sz 16) }

val impl__ZERO:
    #v_Vector: Type0 ->
    {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |} ->
    Prims.unit
  -> Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl__add_error_reduce
      (#v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self error: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl__add_message_error_reduce
      (#v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self message result: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl__add_standard_error_reduce
      (#v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self error: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

/// Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
/// sum of their constituent coefficients.
val impl__add_to_ring_element
      (#v_Vector: Type0)
      (v_K: usize)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self rhs: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl__from_i16_array
      (#v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (a: t_Slice i16)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

/// Given two `KyberPolynomialRingElement`s in their NTT representations,
/// compute their product. Given two polynomials in the NTT domain `f^` and `ĵ`,
/// the `iᵗʰ` coefficient of the product `k̂` is determined by the calculation:
/// ```plaintext
/// ĥ[2·i] + ĥ[2·i + 1]X = (f^[2·i] + f^[2·i + 1]X)·(ĝ[2·i] + ĝ[2·i + 1]X) mod (X² - ζ^(2·BitRev₇(i) + 1))
/// ```
/// This function almost implements <strong>Algorithm 10</strong> of the
/// NIST FIPS 203 standard, which is reproduced below:
/// ```plaintext
/// Input: Two arrays fˆ ∈ ℤ₂₅₆ and ĝ ∈ ℤ₂₅₆.
/// Output: An array ĥ ∈ ℤq.
/// for(i ← 0; i < 128; i++)
///     (ĥ[2i], ĥ[2i+1]) ← BaseCaseMultiply(fˆ[2i], fˆ[2i+1], ĝ[2i], ĝ[2i+1], ζ^(2·BitRev₇(i) + 1))
/// end for
/// return ĥ
/// ```
/// We say "almost" because the coefficients of the ring element output by
/// this function are in the Montgomery domain.
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val impl__ntt_multiply
      (#v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self rhs: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl__poly_barrett_reduce
      (#v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl__subtract_reduce
      (#v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self b: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)
