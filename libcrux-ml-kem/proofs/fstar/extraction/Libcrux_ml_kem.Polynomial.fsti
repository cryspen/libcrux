module Libcrux_ml_kem.Polynomial
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Traits in
  ()

let v_ZETAS_TIMES_MONTGOMERY_R: t_Array i16 (Rust_primitives.mk_usize 128) =
  let _:Prims.unit = assert_norm (pow2 16 == 65536) in
  let list =
    [
      Rust_primitives.mk_i16 (-1044); Rust_primitives.mk_i16 (-758); Rust_primitives.mk_i16 (-359);
      Rust_primitives.mk_i16 (-1517); Rust_primitives.mk_i16 1493; Rust_primitives.mk_i16 1422;
      Rust_primitives.mk_i16 287; Rust_primitives.mk_i16 202; Rust_primitives.mk_i16 (-171);
      Rust_primitives.mk_i16 622; Rust_primitives.mk_i16 1577; Rust_primitives.mk_i16 182;
      Rust_primitives.mk_i16 962; Rust_primitives.mk_i16 (-1202); Rust_primitives.mk_i16 (-1474);
      Rust_primitives.mk_i16 1468; Rust_primitives.mk_i16 573; Rust_primitives.mk_i16 (-1325);
      Rust_primitives.mk_i16 264; Rust_primitives.mk_i16 383; Rust_primitives.mk_i16 (-829);
      Rust_primitives.mk_i16 1458; Rust_primitives.mk_i16 (-1602); Rust_primitives.mk_i16 (-130);
      Rust_primitives.mk_i16 (-681); Rust_primitives.mk_i16 1017; Rust_primitives.mk_i16 732;
      Rust_primitives.mk_i16 608; Rust_primitives.mk_i16 (-1542); Rust_primitives.mk_i16 411;
      Rust_primitives.mk_i16 (-205); Rust_primitives.mk_i16 (-1571); Rust_primitives.mk_i16 1223;
      Rust_primitives.mk_i16 652; Rust_primitives.mk_i16 (-552); Rust_primitives.mk_i16 1015;
      Rust_primitives.mk_i16 (-1293); Rust_primitives.mk_i16 1491; Rust_primitives.mk_i16 (-282);
      Rust_primitives.mk_i16 (-1544); Rust_primitives.mk_i16 516; Rust_primitives.mk_i16 (-8);
      Rust_primitives.mk_i16 (-320); Rust_primitives.mk_i16 (-666); Rust_primitives.mk_i16 (-1618);
      Rust_primitives.mk_i16 (-1162); Rust_primitives.mk_i16 126; Rust_primitives.mk_i16 1469;
      Rust_primitives.mk_i16 (-853); Rust_primitives.mk_i16 (-90); Rust_primitives.mk_i16 (-271);
      Rust_primitives.mk_i16 830; Rust_primitives.mk_i16 107; Rust_primitives.mk_i16 (-1421);
      Rust_primitives.mk_i16 (-247); Rust_primitives.mk_i16 (-951); Rust_primitives.mk_i16 (-398);
      Rust_primitives.mk_i16 961; Rust_primitives.mk_i16 (-1508); Rust_primitives.mk_i16 (-725);
      Rust_primitives.mk_i16 448; Rust_primitives.mk_i16 (-1065); Rust_primitives.mk_i16 677;
      Rust_primitives.mk_i16 (-1275); Rust_primitives.mk_i16 (-1103); Rust_primitives.mk_i16 430;
      Rust_primitives.mk_i16 555; Rust_primitives.mk_i16 843; Rust_primitives.mk_i16 (-1251);
      Rust_primitives.mk_i16 871; Rust_primitives.mk_i16 1550; Rust_primitives.mk_i16 105;
      Rust_primitives.mk_i16 422; Rust_primitives.mk_i16 587; Rust_primitives.mk_i16 177;
      Rust_primitives.mk_i16 (-235); Rust_primitives.mk_i16 (-291); Rust_primitives.mk_i16 (-460);
      Rust_primitives.mk_i16 1574; Rust_primitives.mk_i16 1653; Rust_primitives.mk_i16 (-246);
      Rust_primitives.mk_i16 778; Rust_primitives.mk_i16 1159; Rust_primitives.mk_i16 (-147);
      Rust_primitives.mk_i16 (-777); Rust_primitives.mk_i16 1483; Rust_primitives.mk_i16 (-602);
      Rust_primitives.mk_i16 1119; Rust_primitives.mk_i16 (-1590); Rust_primitives.mk_i16 644;
      Rust_primitives.mk_i16 (-872); Rust_primitives.mk_i16 349; Rust_primitives.mk_i16 418;
      Rust_primitives.mk_i16 329; Rust_primitives.mk_i16 (-156); Rust_primitives.mk_i16 (-75);
      Rust_primitives.mk_i16 817; Rust_primitives.mk_i16 1097; Rust_primitives.mk_i16 603;
      Rust_primitives.mk_i16 610; Rust_primitives.mk_i16 1322; Rust_primitives.mk_i16 (-1285);
      Rust_primitives.mk_i16 (-1465); Rust_primitives.mk_i16 384; Rust_primitives.mk_i16 (-1215);
      Rust_primitives.mk_i16 (-136); Rust_primitives.mk_i16 1218; Rust_primitives.mk_i16 (-1335);
      Rust_primitives.mk_i16 (-874); Rust_primitives.mk_i16 220; Rust_primitives.mk_i16 (-1187);
      Rust_primitives.mk_i16 (-1659); Rust_primitives.mk_i16 (-1185); Rust_primitives.mk_i16 (-1530);
      Rust_primitives.mk_i16 (-1278); Rust_primitives.mk_i16 794; Rust_primitives.mk_i16 (-1510);
      Rust_primitives.mk_i16 (-854); Rust_primitives.mk_i16 (-870); Rust_primitives.mk_i16 478;
      Rust_primitives.mk_i16 (-108); Rust_primitives.mk_i16 (-308); Rust_primitives.mk_i16 996;
      Rust_primitives.mk_i16 991; Rust_primitives.mk_i16 958; Rust_primitives.mk_i16 (-1460);
      Rust_primitives.mk_i16 1522; Rust_primitives.mk_i16 1628
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 128);
  Rust_primitives.Hax.array_of_list 128 list

val get_zeta (i: usize)
    : Prims.Pure i16
      (requires i <. Rust_primitives.mk_usize 128)
      (ensures
        fun result ->
          let result:i16 = result in
          Spec.Utils.is_i16b 1664 result)

let v_VECTORS_IN_RING_ELEMENT: usize =
  Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /!
  Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR

type t_PolynomialRingElement
  (v_Vector: Type0) {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = { f_coefficients:t_Array v_Vector (Rust_primitives.mk_usize 16) }

let to_spec_poly_t (#v_Vector: Type0)
    {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    (p: t_PolynomialRingElement v_Vector) : Spec.MLKEM.polynomial =
    admit()

let to_spec_vector_t (#r:Spec.MLKEM.rank) (#v_Vector: Type0)
    {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    (m:t_Array (t_PolynomialRingElement v_Vector) r) : Spec.MLKEM.vector r =
    createi r (fun i -> to_spec_poly_t #v_Vector (m.[i]))

let to_spec_matrix_t (#r:Spec.MLKEM.rank) (#v_Vector: Type0)
    {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    (m:t_Array (t_Array (t_PolynomialRingElement v_Vector) r) r) : Spec.MLKEM.matrix r =
    createi r (fun i -> to_spec_vector_t #r #v_Vector (m.[i]))

val impl_2__ZERO:
    #v_Vector: Type0 ->
    {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |} ->
    Prims.unit
  -> Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__add_error_reduce
      (#v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self error: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__add_message_error_reduce
      (#v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self message result: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__add_standard_error_reduce
      (#v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self error: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

/// Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
/// sum of their constituent coefficients.
val impl_2__add_to_ring_element
      (#v_Vector: Type0)
      (v_K: usize)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self rhs: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__from_i16_array
      (#v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (a: t_Slice i16)
    : Prims.Pure (t_PolynomialRingElement v_Vector)
      (requires
        (v_VECTORS_IN_RING_ELEMENT *! Rust_primitives.mk_usize 16 <: usize) <=.
        (Core.Slice.impl__len #i16 a <: usize))
      (fun _ -> Prims.l_True)

/// Given two `KyberPolynomialRingElement`s in their NTT representations,
/// compute their product. Given two polynomials in the NTT domain `f^` and `ĵ`,
/// the `iᵗʰ` coefficient of the product `k\u{302}` is determined by the calculation:
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
/// We say \"almost\" because the coefficients of the ring element output by
/// this function are in the Montgomery domain.
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val impl_2__ntt_multiply
      (#v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self rhs: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__poly_barrett_reduce
      (#v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__subtract_reduce
      (#v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self b: t_PolynomialRingElement v_Vector)
    : Prims.Pure (t_PolynomialRingElement v_Vector) Prims.l_True (fun _ -> Prims.l_True)
