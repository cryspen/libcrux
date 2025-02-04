module Libcrux_ml_dsa.Simd.Avx2.Invntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let invert_ntt_montgomery__inv_inner__v_FACTOR: i32 = mk_i32 41978

val simd_unit_invert_ntt_at_layer_0_
      (simd_unit0 simd_unit1: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta00 zeta01 zeta02 zeta03 zeta10 zeta11 zeta12 zeta13: i32)
    : Prims.Pure
      (Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 & Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256
      ) Prims.l_True (fun _ -> Prims.l_True)

let simd_unit_invert_ntt_at_layer_0___v_SHUFFLE: i32 = mk_i32 216

val simd_unit_invert_ntt_at_layer_1_
      (simd_unit0 simd_unit1: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta00 zeta01 zeta10 zeta11: i32)
    : Prims.Pure
      (Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 & Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256
      ) Prims.l_True (fun _ -> Prims.l_True)

val simd_unit_invert_ntt_at_layer_2_
      (simd_unit0 simd_unit1: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta0 zeta1: i32)
    : Prims.Pure
      (Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 & Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256
      ) Prims.l_True (fun _ -> Prims.l_True)

val invert_ntt_at_layer_0___round
      (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (index: usize)
      (zeta00 zeta01 zeta02 zeta03 zeta10 zeta11 zeta12 zeta13: i32)
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_0_ (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_1___round
      (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (index: usize)
      (zeta_00_ zeta_01_ zeta_10_ zeta_11_: i32)
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_1_ (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_2___round
      (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (index: usize)
      (zeta1 zeta2: i32)
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_2_ (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val outer_3_plus
      (v_OFFSET v_STEP_BY: usize)
      (v_ZETA: i32)
      (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_3_ (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

let invert_ntt_at_layer_3___v_STEP: usize = mk_usize 8

let invert_ntt_at_layer_3___v_STEP_BY: usize = mk_usize 1

val invert_ntt_at_layer_4_ (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

let invert_ntt_at_layer_4___v_STEP: usize = mk_usize 16

let invert_ntt_at_layer_4___v_STEP_BY: usize = mk_usize 2

val invert_ntt_at_layer_5_ (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

let invert_ntt_at_layer_5___v_STEP: usize = mk_usize 32

let invert_ntt_at_layer_5___v_STEP_BY: usize = mk_usize 4

val invert_ntt_at_layer_6_ (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

let invert_ntt_at_layer_6___v_STEP: usize = mk_usize 64

let invert_ntt_at_layer_6___v_STEP_BY: usize = mk_usize 8

val invert_ntt_at_layer_7_ (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_montgomery__inv_inner
      (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_montgomery (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

let invert_ntt_at_layer_7___v_STEP: usize = mk_usize 128

let invert_ntt_at_layer_7___v_STEP_BY: usize = mk_usize 16
