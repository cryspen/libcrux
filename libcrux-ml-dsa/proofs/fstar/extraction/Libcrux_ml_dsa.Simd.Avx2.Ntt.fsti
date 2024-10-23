module Libcrux_ml_dsa.Simd.Avx2.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let butterfly_2___SHUFFLE: i32 = 216l

val butterfly_2_
      (a b: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta_a0 zeta_a1 zeta_a2 zeta_a3 zeta_b0 zeta_b1 zeta_b2 zeta_b3: i32)
    : Prims.Pure
      (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256)
      Prims.l_True
      (fun _ -> Prims.l_True)

val butterfly_4_
      (a b: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta_a0 zeta_a1 zeta_b0 zeta_b1: i32)
    : Prims.Pure
      (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256)
      Prims.l_True
      (fun _ -> Prims.l_True)

val butterfly_8_ (a b: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta0 zeta1: i32)
    : Prims.Pure
      (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256)
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_0_
      (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta0 zeta1 zeta2 zeta3: i32)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val invert_ntt_at_layer_1_ (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta0 zeta1: i32)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val invert_ntt_at_layer_2_ (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta: i32)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val ntt_at_layer_3_plus
      (v_LAYER zeta_i: usize)
      (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
    : Prims.Pure (usize & t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_0_ (zeta_i: usize) (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
    : Prims.Pure (usize & t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_1_ (zeta_i: usize) (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
    : Prims.Pure (usize & t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_2_ (zeta_i: usize) (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
    : Prims.Pure (usize & t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
    : Prims.Pure (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)
