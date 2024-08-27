module Libcrux_ml_kem.Vector.Avx2.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let ntt_multiply__PERMUTE_WITH: i32 = 216l

val inv_ntt_layer_1_step
      (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val inv_ntt_layer_2_step (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta0 zeta1: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val inv_ntt_layer_3_step (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val ntt_layer_1_step
      (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      Prims.l_True
      (ensures
        fun result ->
          let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 = result in
          Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 result ==
          Spec.MLKEM.poly_ntt_layer_1_step (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vector)
            zeta0
            zeta1
            zeta2
            zeta3)

val ntt_layer_2_step (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta0 zeta1: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val ntt_layer_3_step (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val ntt_multiply (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)
