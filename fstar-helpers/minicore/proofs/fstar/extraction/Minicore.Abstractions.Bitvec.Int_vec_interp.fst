module Minicore.Abstractions.Bitvec.Int_vec_interp
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

irreducible

/// An F* attribute that marks an item as being an interpretation lemma.
let v_SIMPLIFICATION_LEMMA: Prims.unit = () <: Prims.unit

let e_ee_1: Prims.unit = ()

///Conversion from bit vectors of size 256 to i32 vectors of size 8
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val e_ee_1__impl': Core.Convert.t_From (Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
  (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))

let e_ee_1__impl = e_ee_1__impl'

///Conversion from i32 vectors of size 8to  bit vectors of size 256
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val e_ee_1__impl_1': Core.Convert.t_From (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  (Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

let e_ee_1__impl_1 = e_ee_1__impl_1'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 256 > :: from and then i32x8 :: from is the identity.
assume
val e_ee_1__lemma_cancel_iv': x: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32
  -> Lemma
    (ensures
      (Core.Convert.f_from #(Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
          #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          #FStar.Tactics.Typeclasses.solve
          (Core.Convert.f_from #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
              #(Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              #FStar.Tactics.Typeclasses.solve
              x
            <:
            Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32) ==
      x)

let e_ee_1__lemma_cancel_iv = e_ee_1__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i32x8 :: from and then BitVec :: < 256 > :: from is the identity.
assume
val e_ee_1__lemma_cancel_bv': x: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core.Convert.f_from #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          #(Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
          #FStar.Tactics.Typeclasses.solve
          (Core.Convert.f_from #(Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
              #FStar.Tactics.Typeclasses.solve
              x
            <:
            Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      x)

let e_ee_1__lemma_cancel_bv = e_ee_1__lemma_cancel_bv'

let e_ee_2: Prims.unit = ()

///Conversion from bit vectors of size 256 to i64 vectors of size 4
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val e_ee_2__impl': Core.Convert.t_From (Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
  (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))

let e_ee_2__impl = e_ee_2__impl'

///Conversion from i64 vectors of size 4to  bit vectors of size 256
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val e_ee_2__impl_1': Core.Convert.t_From (Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  (Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

let e_ee_2__impl_1 = e_ee_2__impl_1'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 256 > :: from and then i64x4 :: from is the identity.
assume
val e_ee_2__lemma_cancel_iv': x: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64
  -> Lemma
    (ensures
      (Core.Convert.f_from #(Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
          #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          #FStar.Tactics.Typeclasses.solve
          (Core.Convert.f_from #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
              #(Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
              #FStar.Tactics.Typeclasses.solve
              x
            <:
            Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64) ==
      x)

let e_ee_2__lemma_cancel_iv = e_ee_2__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i64x4 :: from and then BitVec :: < 256 > :: from is the identity.
assume
val e_ee_2__lemma_cancel_bv': x: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core.Convert.f_from #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          #(Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
          #FStar.Tactics.Typeclasses.solve
          (Core.Convert.f_from #(Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
              #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
              #FStar.Tactics.Typeclasses.solve
              x
            <:
            Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      x)

let e_ee_2__lemma_cancel_bv = e_ee_2__lemma_cancel_bv'

let impl__into_i32x8 (self: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    : Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Minicore.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        let value:i64 =
          Minicore.Abstractions.Funarr.impl_5__get (mk_u64 4) #i64 self (i /! mk_u64 2 <: u64)
        in
        cast ((if (i %! mk_u64 2 <: u64) =. mk_u64 0 then value else value >>! mk_i32 32) <: i64)
        <:
        i32)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Convert.t_From (Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
  (Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64) =
  {
    f_from_pre = (fun (vec: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64) -> true);
    f_from_post
    =
    (fun
        (vec: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        (out: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        ->
        true);
    f_from
    =
    fun (vec: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64) -> impl__into_i32x8 vec
  }

[@@ v_SIMPLIFICATION_LEMMA ]

/// Lemma stating that converting an `i64x4` vector to a `BitVec<256>` and then into an `i32x8`
/// yields the same result as directly converting the `i64x4` into an `i32x8`.
assume
val lemma_rewrite_i64x4_bv_i32x8': bv: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64
  -> Lemma
    (ensures
      (Core.Convert.f_from #(Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
          #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          #FStar.Tactics.Typeclasses.solve
          (Core.Convert.f_from #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
              #(Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
              #FStar.Tactics.Typeclasses.solve
              bv
            <:
            Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32) ==
      (impl__into_i32x8 bv <: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32))

let lemma_rewrite_i64x4_bv_i32x8 = lemma_rewrite_i64x4_bv_i32x8'
