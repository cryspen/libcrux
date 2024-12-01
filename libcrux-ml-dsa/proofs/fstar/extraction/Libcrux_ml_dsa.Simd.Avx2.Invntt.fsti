module Libcrux_ml_dsa.Simd.Avx2.Invntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let invert_ntt_at_layer_3___STEP: usize = sz 8

let invert_ntt_at_layer_3___STEP_BY: usize = sz 1

let invert_ntt_at_layer_4___STEP: usize = sz 16

let invert_ntt_at_layer_4___STEP_BY: usize = sz 2

let invert_ntt_at_layer_5___STEP: usize = sz 32

let invert_ntt_at_layer_5___STEP_BY: usize = sz 4

let invert_ntt_at_layer_6___STEP: usize = sz 64

let invert_ntt_at_layer_6___STEP_BY: usize = sz 8

let invert_ntt_at_layer_7___STEP: usize = sz 128

let invert_ntt_at_layer_7___STEP_BY: usize = sz 16

let simd_unit_invert_ntt_at_layer_0___SHUFFLE: i32 = 216l

val simd_unit_invert_ntt_at_layer_0_
      (simd_unit0 simd_unit1: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta00 zeta01 zeta02 zeta03 zeta10 zeta11 zeta12 zeta13: i32)
    : Prims.Pure
      (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256)
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_0___round
      (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      (index: usize)
      (zeta00 zeta01 zeta02 zeta03 zeta10 zeta11 zeta12 zeta13: i32)
    : Prims.Pure (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_0_ (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
    : Prims.Pure (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val simd_unit_invert_ntt_at_layer_1_
      (simd_unit0 simd_unit1: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta00 zeta01 zeta10 zeta11: i32)
    : Prims.Pure
      (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256)
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_1___round
      (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      (index: usize)
      (zeta_00_ zeta_01_ zeta_10_ zeta_11_: i32)
    : Prims.Pure (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_1_ (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
    : Prims.Pure (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val simd_unit_invert_ntt_at_layer_2_
      (simd_unit0 simd_unit1: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta0 zeta1: i32)
    : Prims.Pure
      (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256)
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_2___round
      (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      (index: usize)
      (zeta1 zeta2: i32)
    : Prims.Pure (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_2_ (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
    : Prims.Pure (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val outer_3_plus
      (v_OFFSET v_STEP_BY: usize)
      (v_ZETA: i32)
      (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
    : Prims.Pure (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_3_ (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
    : Prims.Pure (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_4_ (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
    : Prims.Pure (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_5_ (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
    : Prims.Pure (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_6_ (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
    : Prims.Pure (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_7_ (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
    : Prims.Pure (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_montgomery (re: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
    : Prims.Pure (t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)
