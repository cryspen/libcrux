module Libcrux_ml_kem.Polynomial
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Traits in
  ()

let v_ZETAS_TIMES_MONTGOMERY_R: t_Array i16 (sz 128) =
  let list =
    [
      (-1044s); (-758s); (-359s); (-1517s); 1493s; 1422s; 287s; 202s; (-171s); 622s; 1577s; 182s;
      962s; (-1202s); (-1474s); 1468s; 573s; (-1325s); 264s; 383s; (-829s); 1458s; (-1602s); (-130s);
      (-681s); 1017s; 732s; 608s; (-1542s); 411s; (-205s); (-1571s); 1223s; 652s; (-552s); 1015s;
      (-1293s); 1491s; (-282s); (-1544s); 516s; (-8s); (-320s); (-666s); (-1618s); (-1162s); 126s;
      1469s; (-853s); (-90s); (-271s); 830s; 107s; (-1421s); (-247s); (-951s); (-398s); 961s;
      (-1508s); (-725s); 448s; (-1065s); 677s; (-1275s); (-1103s); 430s; 555s; 843s; (-1251s); 871s;
      1550s; 105s; 422s; 587s; 177s; (-235s); (-291s); (-460s); 1574s; 1653s; (-246s); 778s; 1159s;
      (-147s); (-777s); 1483s; (-602s); 1119s; (-1590s); 644s; (-872s); 349s; 418s; 329s; (-156s);
      (-75s); 817s; 1097s; 603s; 610s; 1322s; (-1285s); (-1465s); 384s; (-1215s); (-136s); 1218s;
      (-1335s); (-874s); 220s; (-1187s); (-1659s); (-1185s); (-1530s); (-1278s); 794s; (-1510s);
      (-854s); (-870s); 478s; (-108s); (-308s); 996s; 991s; 958s; (-1460s); 1522s; 1628s
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 128);
  Rust_primitives.Hax.array_of_list 128 list

let v_VECTORS_IN_RING_ELEMENT: usize =
  Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /!
  Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR

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
