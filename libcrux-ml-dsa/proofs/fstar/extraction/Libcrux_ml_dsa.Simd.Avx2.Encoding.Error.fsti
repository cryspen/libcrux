module Libcrux_ml_dsa.Simd.Avx2.Encoding.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let serialize_when_eta_is_2___v_ETA: i32 = mk_i32 2

val serialize_when_eta_is_2_
      (simd_unit: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (out: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

let serialize_when_eta_is_4___v_ETA: i32 = mk_i32 4

val serialize_when_eta_is_4_
      (simd_unit: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (out: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

val serialize
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (simd_unit: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

let deserialize_to_unsigned_when_eta_is_2___v_COEFFICIENT_MASK: i32 =
  (mk_i32 1 <<! mk_i32 3 <: i32) -! mk_i32 1

val deserialize_to_unsigned_when_eta_is_2_ (bytes: t_Slice u8)
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      Prims.l_True
      (fun _ -> Prims.l_True)

let deserialize_to_unsigned_when_eta_is_4___v_COEFFICIENT_MASK: i32 =
  (mk_i32 1 <<! mk_i32 4 <: i32) -! mk_i32 1

val deserialize_to_unsigned_when_eta_is_4_ (bytes: t_Slice u8)
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_to_unsigned (eta: Libcrux_ml_dsa.Constants.t_Eta) (serialized: t_Slice u8)
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (serialized: t_Slice u8)
      (out: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      Prims.l_True
      (fun _ -> Prims.l_True)
