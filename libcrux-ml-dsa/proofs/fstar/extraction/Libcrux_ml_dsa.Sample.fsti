module Libcrux_ml_dsa.Sample
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

val rejection_sample_less_than_field_modulus
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (randomness: t_Slice u8)
      (sampled_coefficients: usize)
      (out: t_Array i32 (mk_usize 263))
    : Prims.Pure (usize & t_Array i32 (mk_usize 263) & bool) Prims.l_True (fun _ -> Prims.l_True)

val generate_domain_separator: (u8 & u8) -> Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

val add_domain_separator (slice: t_Slice u8) (indices: (u8 & u8))
    : Prims.Pure (t_Array u8 (mk_usize 34)) Prims.l_True (fun _ -> Prims.l_True)

val sample_up_to_four_ring_elements_flat__xy (index width: usize)
    : Prims.Pure (u8 & u8) Prims.l_True (fun _ -> Prims.l_True)

/// Sample and write out up to four ring elements.
/// If i <= `elements_requested`, a field element with domain separated
/// seed according to the provided index is generated in
/// `tmp_stack[i]`. After successful rejection sampling in
/// `tmp_stack[i]`, the ring element is written to `matrix` at the
/// provided index in `indices[i]`.
/// `rand_stack` is a working buffer that holds initial Shake output.
val sample_up_to_four_ring_elements_flat
      (#v_SIMDUnit #v_Shake128: Type0)
      {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i3: Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128 |}
      (columns: usize)
      (seed: t_Slice u8)
      (matrix: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (rand_stack0 rand_stack1 rand_stack2 rand_stack3: t_Array u8 (mk_usize 840))
      (tmp_stack: t_Slice (t_Array i32 (mk_usize 263)))
      (start_index elements_requested: usize)
    : Prims.Pure
      (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
        t_Array u8 (mk_usize 840) &
        t_Array u8 (mk_usize 840) &
        t_Array u8 (mk_usize 840) &
        t_Array u8 (mk_usize 840) &
        t_Slice (t_Array i32 (mk_usize 263))) Prims.l_True (fun _ -> Prims.l_True)

val rejection_sample_less_than_eta_equals_2_
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (randomness: t_Slice u8)
      (sampled_coefficients: usize)
      (out: t_Array i32 (mk_usize 263))
    : Prims.Pure (usize & t_Array i32 (mk_usize 263) & bool) Prims.l_True (fun _ -> Prims.l_True)

val rejection_sample_less_than_eta_equals_4_
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (randomness: t_Slice u8)
      (sampled_coefficients: usize)
      (out: t_Array i32 (mk_usize 263))
    : Prims.Pure (usize & t_Array i32 (mk_usize 263) & bool) Prims.l_True (fun _ -> Prims.l_True)

val rejection_sample_less_than_eta
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (randomness: t_Slice u8)
      (sampled: usize)
      (out: t_Array i32 (mk_usize 263))
    : Prims.Pure (usize & t_Array i32 (mk_usize 263) & bool) Prims.l_True (fun _ -> Prims.l_True)

val add_error_domain_separator (slice: t_Slice u8) (domain_separator: u16)
    : Prims.Pure (t_Array u8 (mk_usize 66)) Prims.l_True (fun _ -> Prims.l_True)

val sample_four_error_ring_elements
      (#v_SIMDUnit #v_Shake256: Type0)
      {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i3: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256 |}
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (seed: t_Slice u8)
      (start_index: u16)
      (re: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
    : Prims.Pure (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      Prims.l_True
      (fun _ -> Prims.l_True)

val sample_mask_ring_element
      (#v_SIMDUnit #v_Shake256: Type0)
      {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i3: Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256 |}
      (seed: t_Array u8 (mk_usize 66))
      (result: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (gamma1_exponent: usize)
    : Prims.Pure (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sample_mask_vector
      (#v_SIMDUnit #v_Shake256 #v_Shake256X4: Type0)
      {| i3: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i4: Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256 |}
      {| i5: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4 |}
      (dimension gamma1_exponent: usize)
      (seed: t_Array u8 (mk_usize 64))
      (domain_separator: u16)
      (mask: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
    : Prims.Pure (u16 & t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      Prims.l_True
      (fun _ -> Prims.l_True)

val inside_out_shuffle
      (randomness: t_Slice u8)
      (out_index: usize)
      (signs: u64)
      (result: t_Array i32 (mk_usize 256))
    : Prims.Pure (usize & u64 & t_Array i32 (mk_usize 256) & bool)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sample_challenge_ring_element
      (#v_SIMDUnit #v_Shake256: Type0)
      {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i3: Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256 |}
      (seed: t_Slice u8)
      (number_of_ones: usize)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Prims.Pure (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)
