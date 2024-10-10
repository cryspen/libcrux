module Libcrux_ml_kem.Vector.Avx2.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val mulhi_mm256_epi32 (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val compress_ciphertext_coefficient
      (v_COEFFICIENT_BITS: i32)
      (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires
        v v_COEFFICIENT_BITS >= 0 /\ v v_COEFFICIENT_BITS < bits i32_inttype /\
        range (v ((mk_i32 1) <<! v_COEFFICIENT_BITS) - 1) i32_inttype)
      (fun _ -> Prims.l_True)

val compress_message_coefficient (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val decompress_ciphertext_coefficient
      (v_COEFFICIENT_BITS: i32)
      (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256
      (requires v v_COEFFICIENT_BITS >= 0 /\ v v_COEFFICIENT_BITS < bits i32_inttype)
      (fun _ -> Prims.l_True)
