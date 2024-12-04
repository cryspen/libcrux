module Libcrux_ml_dsa.Simd.Avx2.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let butterfly_2___SHUFFLE: i32 = 216l

let ntt_at_layer_5_to_3___STEP: usize = sz 1 <<! 5l

let ntt_at_layer_5_to_3___STEP_1: usize = sz 1 <<! 4l

let ntt_at_layer_5_to_3___STEP_2: usize = sz 1 <<! 3l

val ntt_at_layer_7_and_6___mul
      (re: t_Array u8 (sz 32))
      (index: usize)
      (zeta: u8)
      (step_by: usize)
      (field_modulus inverse_of_modulus_mod_montgomery_r: u8)
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

let ntt_at_layer_5_to_3___STEP_BY: usize =
  ntt_at_layer_5_to_3___STEP /! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT

let ntt_at_layer_5_to_3___STEP_BY_1: usize =
  ntt_at_layer_5_to_3___STEP_1 /! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT

let ntt_at_layer_5_to_3___STEP_BY_2: usize =
  ntt_at_layer_5_to_3___STEP_2 /! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT

let ntt_at_layer_7_and_6___STEP_BY_6_: usize =
  (sz 1 <<! 6l <: usize) /! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT

let ntt_at_layer_7_and_6___STEP_BY_7_: usize =
  sz 2 *! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT

val butterfly_2_ (a b: u8) (zeta_a0 zeta_a1 zeta_a2 zeta_a3 zeta_b0 zeta_b1 zeta_b2 zeta_b3: i32)
    : Prims.Pure (u8 & u8) Prims.l_True (fun _ -> Prims.l_True)

val butterfly_4_ (a b: u8) (zeta_a0 zeta_a1 zeta_b0 zeta_b1: i32)
    : Prims.Pure (u8 & u8) Prims.l_True (fun _ -> Prims.l_True)

val butterfly_8_ (a b: u8) (zeta0 zeta1: i32)
    : Prims.Pure (u8 & u8) Prims.l_True (fun _ -> Prims.l_True)

val ntt_at_layer_0___round
      (re: t_Array u8 (sz 32))
      (index: usize)
      (zeta_0_ zeta_1_ zeta_2_ zeta_3_ zeta_4_ zeta_5_ zeta_6_ zeta_7_: i32)
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val ntt_at_layer_0_ (re: t_Array u8 (sz 32))
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val ntt_at_layer_1___round
      (re: t_Array u8 (sz 32))
      (index: usize)
      (zeta_0_ zeta_1_ zeta_2_ zeta_3_: i32)
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val ntt_at_layer_1_ (re: t_Array u8 (sz 32))
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val ntt_at_layer_2___round (re: t_Array u8 (sz 32)) (index: usize) (zeta_0_ zeta_1_: i32)
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val ntt_at_layer_2_ (re: t_Array u8 (sz 32))
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

/// This is equivalent to the pqclean 0 and 1
/// This does 32 Montgomery multiplications (192 multiplications).
/// This is the same as in pqclean. The only difference is locality of registers.
val ntt_at_layer_7_and_6_ (re: t_Array u8 (sz 32))
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val ntt_at_layer_5_to_3___round
      (v_STEP v_STEP_BY: usize)
      (re: t_Array u8 (sz 32))
      (index: usize)
      (zeta: i32)
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

/// Layer 5, 4, 3
/// Each layer does 16 Montgomery multiplications -> 3*16 = 48 total
/// pqclean does 4 * 4 on each layer -> 48 total | plus 4 * 4 shuffles every time (48)
val ntt_at_layer_5_to_3_ (re: t_Array u8 (sz 32))
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val ntt (re: t_Array u8 (sz 32))
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)
