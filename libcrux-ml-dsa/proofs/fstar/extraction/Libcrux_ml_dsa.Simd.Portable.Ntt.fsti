module Libcrux_ml_dsa.Simd.Portable.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val invert_ntt_at_layer_0_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
      (zeta0 zeta1 zeta2 zeta3: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_1_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
      (zeta0 zeta1: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_2_ (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit) (zeta: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_0_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
      (zeta0 zeta1 zeta2 zeta3: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_1_ (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit) (zeta1 zeta2: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_2_ (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit) (zeta: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)
