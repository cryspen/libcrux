module Libcrux_ml_dsa.Simd.Avx2.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val invert_ntt_at_layer_0_
      (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta0 zeta1 zeta2 zeta3: i32)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val invert_ntt_at_layer_1_ (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta0 zeta1: i32)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val invert_ntt_at_layer_2_ (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta: i32)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val ntt_at_layer_0_
      (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta0 zeta1 zeta2 zeta3: i32)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val ntt_at_layer_1_ (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta0 zeta1: i32)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val ntt_at_layer_2_ (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta: i32)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
