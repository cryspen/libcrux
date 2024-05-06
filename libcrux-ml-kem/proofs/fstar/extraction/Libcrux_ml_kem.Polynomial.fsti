module Libcrux_ml_kem.Polynomial
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_ZETAS_TIMES_MONTGOMERY_R: t_Array i32 (sz 128) =
  let list =
    [
      (-1044l); (-758l); (-359l); (-1517l); 1493l; 1422l; 287l; 202l; (-171l); 622l; 1577l; 182l;
      962l; (-1202l); (-1474l); 1468l; 573l; (-1325l); 264l; 383l; (-829l); 1458l; (-1602l); (-130l);
      (-681l); 1017l; 732l; 608l; (-1542l); 411l; (-205l); (-1571l); 1223l; 652l; (-552l); 1015l;
      (-1293l); 1491l; (-282l); (-1544l); 516l; (-8l); (-320l); (-666l); (-1618l); (-1162l); 126l;
      1469l; (-853l); (-90l); (-271l); 830l; 107l; (-1421l); (-247l); (-951l); (-398l); 961l;
      (-1508l); (-725l); 448l; (-1065l); 677l; (-1275l); (-1103l); 430l; 555l; 843l; (-1251l); 871l;
      1550l; 105l; 422l; 587l; 177l; (-235l); (-291l); (-460l); 1574l; 1653l; (-246l); 778l; 1159l;
      (-147l); (-777l); 1483l; (-602l); 1119l; (-1590l); 644l; (-872l); 349l; 418l; 329l; (-156l);
      (-75l); 817l; 1097l; 603l; 610l; 1322l; (-1285l); (-1465l); 384l; (-1215l); (-136l); 1218l;
      (-1335l); (-874l); 220l; (-1187l); (-1659l); (-1185l); (-1530l); (-1278l); 794l; (-1510l);
      (-854l); (-870l); 478l; (-108l); (-308l); 996l; 991l; 958l; (-1460l); 1522l; 1628l
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 128);
  Rust_primitives.Hax.array_of_list 128 list

val inv_ntt_layer_int_vec_step
      (#v_Vector: Type)
      {| i1: Libcrux_traits.t_Operations v_Vector |}
      (a b: v_Vector)
      (zeta_r: i32)
    : Prims.Pure (v_Vector & v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val ntt_layer_7_int_vec_step
      (#v_Vector: Type)
      {| i1: Libcrux_traits.t_Operations v_Vector |}
      (a b: v_Vector)
    : Prims.Pure (v_Vector & v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val ntt_layer_int_vec_step
      (#v_Vector: Type)
      {| i1: Libcrux_traits.t_Operations v_Vector |}
      (a b: v_Vector)
      (zeta_r: i32)
    : Prims.Pure (v_Vector & v_Vector) Prims.l_True (fun _ -> Prims.l_True)

let v_VECTORS_IN_RING_ELEMENT: usize =
  Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /!
  Libcrux_traits.v_FIELD_ELEMENTS_IN_VECTOR

type t_PolynomialRingElement (v_Vector: Type) {| i1: Libcrux_traits.t_Operations v_Vector |} = {
  f_coefficients:t_Array v_Vector (sz 32)
}

val impl__ZERO: #v_Vector: Type -> {| i1: Libcrux_traits.t_Operations v_Vector |} -> Prims.unit
  -> Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl__add_error_reduce
      (#v_Vector: Type)
      {| i2: Libcrux_traits.t_Operations v_Vector |}
      (self result: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl__add_message_error_reduce
      (#v_Vector: Type)
      {| i2: Libcrux_traits.t_Operations v_Vector |}
      (self message result: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl__add_standard_error_reduce
      (#v_Vector: Type)
      {| i2: Libcrux_traits.t_Operations v_Vector |}
      (self result: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

/// Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
/// sum of their constituent coefficients.
val impl__add_to_ring_element
      (#v_Vector: Type)
      (v_K: usize)
      {| i2: Libcrux_traits.t_Operations v_Vector |}
      (self rhs: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl__from_i32_array
      (#v_Vector: Type)
      {| i2: Libcrux_traits.t_Operations v_Vector |}
      (a: t_Array i32 (sz 256))
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
      (#v_Vector: Type)
      {| i2: Libcrux_traits.t_Operations v_Vector |}
      (self rhs: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl__poly_barrett_reduce
      (#v_Vector: Type)
      {| i2: Libcrux_traits.t_Operations v_Vector |}
      (self: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl__subtract_reduce
      (#v_Vector: Type)
      {| i2: Libcrux_traits.t_Operations v_Vector |}
      (self b: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val invert_ntt_at_layer_1_
      (#v_Vector: Type)
      {| i1: Libcrux_traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: t_PolynomialRingElement v_Vector)
      (v__layer: usize)
    : Prims.Pure (usize & t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val invert_ntt_at_layer_2_
      (#v_Vector: Type)
      {| i1: Libcrux_traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: t_PolynomialRingElement v_Vector)
      (v__layer: usize)
    : Prims.Pure (usize & t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val invert_ntt_at_layer_3_plus
      (#v_Vector: Type)
      {| i1: Libcrux_traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: t_PolynomialRingElement v_Vector)
      (layer: usize)
    : Prims.Pure (usize & t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

/// Represents an intermediate polynomial splitting step in the NTT. All
/// resulting coefficients are in the normal domain since the zetas have been
/// multiplied by MONTGOMERY_R.
val ntt_at_layer_1_
      (#v_Vector: Type)
      {| i1: Libcrux_traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: t_PolynomialRingElement v_Vector)
      (v__layer v__initial_coefficient_bound: usize)
    : Prims.Pure (usize & t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val ntt_at_layer_2_
      (#v_Vector: Type)
      {| i1: Libcrux_traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: t_PolynomialRingElement v_Vector)
      (v__layer v__initial_coefficient_bound: usize)
    : Prims.Pure (usize & t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val ntt_at_layer_3_plus
      (#v_Vector: Type)
      {| i1: Libcrux_traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: t_PolynomialRingElement v_Vector)
      (layer v__initial_coefficient_bound: usize)
    : Prims.Pure (usize & t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val ntt_at_layer_7_
      (#v_Vector: Type)
      {| i1: Libcrux_traits.t_Operations v_Vector |}
      (re: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)
