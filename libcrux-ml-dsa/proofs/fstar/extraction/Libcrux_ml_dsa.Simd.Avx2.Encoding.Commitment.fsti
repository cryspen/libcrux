module Libcrux_ml_dsa.Simd.Avx2.Encoding.Commitment
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val serialize_6_ (simd_unit: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure
      (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) &
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_4___aux (simd_unit: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
      Prims.l_True
      (fun _ -> Prims.l_True)

val serialize_4_ (simd_unit: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
      Prims.l_True
      (ensures
        fun r ->
          let r:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) = r in
          let r:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
            Core.Convert.f_from #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
              #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128))
              #FStar.Tactics.Typeclasses.solve
              r
          in
          let simd_unit:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
            Core.Convert.f_from #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
              #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
              #FStar.Tactics.Typeclasses.solve
              simd_unit
          in
          forall (i: u64).
            b2t (i <. mk_u64 32 <: bool) ==>
            b2t
            ((r.[ i ] <: Minicore.Abstractions.Bit.t_Bit) =.
              (simd_unit.[ ((i /! mk_u64 4 <: u64) *! mk_u64 32 <: u64) +! (i %! mk_u64 4 <: u64)
                  <:
                  u64 ]
                <:
                Minicore.Abstractions.Bit.t_Bit)
              <:
              bool))

val serialize (simd_unit: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (Core.Slice.impl__len #u8 out <: usize) =. mk_usize 4 ||
        (Core.Slice.impl__len #u8 out <: usize) =. mk_usize 6)
      (fun _ -> Prims.l_True)
