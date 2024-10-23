module Libcrux_ml_dsa.Simd.Avx2.Encoding.Commitment
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val serialize (v_OUTPUT_SIZE: usize) (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure (t_Array u8 v_OUTPUT_SIZE) Prims.l_True (fun _ -> Prims.l_True)
