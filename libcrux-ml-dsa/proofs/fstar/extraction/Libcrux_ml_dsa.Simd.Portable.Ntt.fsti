module Libcrux_ml_dsa.Simd.Portable.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

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

val simd_unit_ntt_at_layer_1_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
      (zeta1 zeta2: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val simd_unit_ntt_at_layer_2_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
      (zeta: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_0_
      (zeta_i: usize)
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
    : Prims.Pure
      (usize & t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_1_
      (zeta_i: usize)
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
    : Prims.Pure
      (usize & t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_2_
      (zeta_i: usize)
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
    : Prims.Pure
      (usize & t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_3_plus
      (v_LAYER zeta_i: usize)
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
    : Prims.Pure
      (usize & t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)
