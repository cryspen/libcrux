module Libcrux_ml_dsa.Simd.Portable.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val simd_unit_ntt_at_layer_0_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (zeta0 zeta1 zeta2 zeta3: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      Prims.l_True
      (fun _ -> Prims.l_True)

val simd_unit_ntt_at_layer_1_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (zeta1 zeta2: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      Prims.l_True
      (fun _ -> Prims.l_True)

val simd_unit_ntt_at_layer_2_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (zeta: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_0___round
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (index: usize)
      (zeta_0_ zeta_1_ zeta_2_ zeta_3_: i32)
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_0_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_1___round
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (index: usize)
      (zeta_0_ zeta_1_: i32)
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_1_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_2___round
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (index: usize)
      (zeta: i32)
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_2_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val outer_3_plus
      (v_OFFSET v_STEP_BY: usize)
      (v_ZETA: i32)
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_3_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

let ntt_at_layer_3___STEP: usize = mk_usize 8

let ntt_at_layer_3___STEP_BY: usize = mk_usize 1

val ntt_at_layer_4_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

let ntt_at_layer_4___STEP: usize = mk_usize 16

let ntt_at_layer_4___STEP_BY: usize = mk_usize 2

val ntt_at_layer_5_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

let ntt_at_layer_5___STEP: usize = mk_usize 32

let ntt_at_layer_5___STEP_BY: usize = mk_usize 4

val ntt_at_layer_6_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

let ntt_at_layer_6___STEP: usize = mk_usize 64

let ntt_at_layer_6___STEP_BY: usize = mk_usize 8

val ntt_at_layer_7_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

let ntt_at_layer_7___STEP: usize = mk_usize 128

let ntt_at_layer_7___STEP_BY: usize = mk_usize 16

val ntt (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)
