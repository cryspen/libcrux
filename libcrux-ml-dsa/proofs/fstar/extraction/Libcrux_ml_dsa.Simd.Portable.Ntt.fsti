module Libcrux_ml_dsa.Simd.Portable.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let ntt_at_layer_3___STEP: usize = sz 8

let ntt_at_layer_3___STEP_BY: usize = sz 1

let ntt_at_layer_4___STEP: usize = sz 16

let ntt_at_layer_4___STEP_BY: usize = sz 2

let ntt_at_layer_5___STEP: usize = sz 32

let ntt_at_layer_5___STEP_BY: usize = sz 4

let ntt_at_layer_6___STEP: usize = sz 64

let ntt_at_layer_6___STEP_BY: usize = sz 8

let ntt_at_layer_7___STEP: usize = sz 128

let ntt_at_layer_7___STEP_BY: usize = sz 16

val invert_ntt_at_layer_0_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
      (zeta0 zeta1 zeta2 zeta3: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_1_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
      (zeta0 zeta1: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_2_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
      (zeta: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val simd_unit_ntt_at_layer_0_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
      (zeta0 zeta1 zeta2 zeta3: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_0___round
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      (index: usize)
      (zeta_0_ zeta_1_ zeta_2_ zeta_3_: i32)
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_0_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val simd_unit_ntt_at_layer_1_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
      (zeta1 zeta2: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_1___round
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      (index: usize)
      (zeta_0_ zeta_1_: i32)
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_1_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val simd_unit_ntt_at_layer_2_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
      (zeta: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_2___round
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      (index: usize)
      (zeta: i32)
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_2_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val outer_3_plus
      (v_OFFSET v_STEP_BY: usize)
      (v_ZETA: i32)
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_3_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_4_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_5_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_6_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_7_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)
