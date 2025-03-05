module Libcrux_ml_dsa.Simd.Avx2.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val to_unsigned_representatives_ret (t: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      Prims.l_True
      (fun _ -> Prims.l_True)

val to_unsigned_representatives (t: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      Prims.l_True
      (fun _ -> Prims.l_True)

val add (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      Prims.l_True
      (fun _ -> Prims.l_True)

val subtract (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      Prims.l_True
      (fun _ -> Prims.l_True)

val montgomery_multiply_by_constant
      (lhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (constant: i32)
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      Prims.l_True
      (fun _ -> Prims.l_True)

val montgomery_multiply (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      Prims.l_True
      (fun _ -> Prims.l_True)

val shift_left_then_reduce
      (v_SHIFT_BY: i32)
      (simd_unit: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      Prims.l_True
      (fun _ -> Prims.l_True)

val infinity_norm_exceeds
      (simd_unit: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (bound: i32)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val power2round (r0 r1: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure
      (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) Prims.l_True (fun _ -> Prims.l_True)

val decompose (gamma2: i32) (r r0 r1: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure
      (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) Prims.l_True (fun _ -> Prims.l_True)

val compute_hint
      (low high: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (gamma2: i32)
      (hint: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) & usize)
      Prims.l_True
      (fun _ -> Prims.l_True)

val uuse_hint (gamma2: i32) (r hint: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      Prims.l_True
      (fun _ -> Prims.l_True)
