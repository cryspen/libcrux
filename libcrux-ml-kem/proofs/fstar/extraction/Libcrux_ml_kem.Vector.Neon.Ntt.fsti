module Libcrux_ml_kem.Vector.Neon.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val inv_ntt_layer_1_step
      (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (zeta1 zeta2 zeta3 zeta4: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val inv_ntt_layer_2_step
      (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (zeta1 zeta2: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val inv_ntt_layer_3_step (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (zeta: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_layer_1_step
      (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (zeta1 zeta2 zeta3 zeta4: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_layer_2_step (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (zeta1 zeta2: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_layer_3_step (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector) (zeta: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_multiply
      (lhs rhs: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (zeta1 zeta2 zeta3 zeta4: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)
