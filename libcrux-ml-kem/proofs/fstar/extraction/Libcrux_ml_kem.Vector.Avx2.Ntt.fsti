module Libcrux_ml_kem.Vector.Avx2.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let ntt_multiply__PERMUTE_WITH: i32 = mk_i32 216

val inv_ntt_layer_1_step
      (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires
        Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
        Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3)
      (fun _ -> Prims.l_True)

val inv_ntt_layer_2_step (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta0 zeta1: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1)
      (fun _ -> Prims.l_True)

val inv_ntt_layer_3_step (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires Spec.Utils.is_i16b 1664 zeta)
      (fun _ -> Prims.l_True)

val ntt_layer_1_step
      (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires
        Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
        Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3)
      (fun _ -> Prims.l_True)

val ntt_layer_2_step (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta0 zeta1: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1)
      (fun _ -> Prims.l_True)

val ntt_layer_3_step (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires Spec.Utils.is_i16b 1664 zeta)
      (fun _ -> Prims.l_True)

val ntt_multiply (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires
        Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
        Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3)
      (fun _ -> Prims.l_True)
