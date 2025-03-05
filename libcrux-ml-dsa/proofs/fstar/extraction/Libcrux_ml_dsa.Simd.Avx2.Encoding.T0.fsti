module Libcrux_ml_dsa.Simd.Avx2.Encoding.T0
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val change_interval (simd_unit: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      Prims.l_True
      (fun _ -> Prims.l_True)

val serialize (simd_unit: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) (out: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

let deserialize__v_COEFFICIENT_MASK: i32 = (mk_i32 1 <<! mk_i32 13 <: i32) -! mk_i32 1

val deserialize (serialized: t_Slice u8) (out: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      Prims.l_True
      (fun _ -> Prims.l_True)
