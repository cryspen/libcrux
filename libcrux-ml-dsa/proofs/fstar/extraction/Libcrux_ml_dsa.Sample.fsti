module Libcrux_ml_dsa.Sample
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Portable in
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

val update_seed (seed: t_Array u8 (sz 66)) (domain_separator: u16)
    : Prims.Pure (u16 & t_Array u8 (sz 66)) Prims.l_True (fun _ -> Prims.l_True)

val rejection_sample_less_than_eta_equals_2_
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (randomness: t_Slice u8)
      (sampled_coefficients: usize)
      (out: t_Array i32 (sz 263))
    : Prims.Pure (usize & t_Array i32 (sz 263) & bool) Prims.l_True (fun _ -> Prims.l_True)

val rejection_sample_less_than_eta_equals_4_
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (randomness: t_Slice u8)
      (sampled_coefficients: usize)
      (out: t_Array i32 (sz 263))
    : Prims.Pure (usize & t_Array i32 (sz 263) & bool) Prims.l_True (fun _ -> Prims.l_True)

val rejection_sample_less_than_eta
      (#v_SIMDUnit: Type0)
      (v_ETA: usize)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (randomness: t_Slice u8)
      (sampled: usize)
      (out: t_Array i32 (sz 263))
    : Prims.Pure (usize & t_Array i32 (sz 263) & bool) Prims.l_True (fun _ -> Prims.l_True)

val rejection_sample_less_than_field_modulus
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (randomness: t_Slice u8)
      (sampled_coefficients: usize)
      (out: t_Array i32 (sz 263))
    : Prims.Pure (usize & t_Array i32 (sz 263) & bool) Prims.l_True (fun _ -> Prims.l_True)

val inside_out_shuffle
      (randomness: t_Slice u8)
      (out_index: usize)
      (signs: u64)
      (result: t_Array i32 (sz 256))
    : Prims.Pure (usize & u64 & t_Array i32 (sz 256) & bool) Prims.l_True (fun _ -> Prims.l_True)

val sample_challenge_ring_element
      (#v_SIMDUnit #v_Shake256: Type0)
      (v_NUMBER_OF_ONES v_SEED_SIZE: usize)
      {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i3: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256 |}
      (seed: t_Array u8 v_SEED_SIZE)
    : Prims.Pure (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sample_four_error_ring_elements
      (#v_SIMDUnit #v_Shake256: Type0)
      (v_ETA: usize)
      {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i3: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256 |}
      (seed_base: t_Array u8 (sz 66))
      (domain_separator0 domain_separator1 domain_seperator2 domain_separator3: u16)
    : Prims.Pure
      (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sample_four_ring_elements
      (#v_SIMDUnit: Type0)
      {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      (seed0: t_Array u8 (sz 34))
      (domain_separator0 domain_separator1 domain_seperator2 domain_separator3: u16)
    : Prims.Pure
      (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sample_mask_ring_element
      (#v_SIMDUnit #v_Shake256: Type0)
      (v_GAMMA1_EXPONENT: usize)
      {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i3: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256 |}
      (seed: t_Array u8 (sz 66))
    : Prims.Pure (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sample_mask_vector
      (#v_SIMDUnit #v_Shake256 #v_Shake256X4: Type0)
      (v_DIMENSION v_GAMMA1_EXPONENT: usize)
      {| i3: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i4: Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256 |}
      {| i5: Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4 |}
      (seed: t_Array u8 (sz 66))
      (domain_separator: u16)
    : Prims.Pure
      (u16 & t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
      Prims.l_True
      (fun _ -> Prims.l_True)
