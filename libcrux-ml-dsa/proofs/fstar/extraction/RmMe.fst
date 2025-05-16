module RmMe
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

module BV_LEMMAS = Core_models.Abstractions.Bitvec.Int_vec_interp


///Lemma that asserts that applying BitVec :: < 256 > :: from and then i32x8 :: from is the identity.
let e_ee_1__lemma_cancel_iv'
  (x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32) 
  arg
  : Lemma
      (ensures
        (BV_LEMMAS.e_ee_1__impl__to_i32x8 (BV_LEMMAS.e_ee_1__impl__from_i32x8 x
              <:
              Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32) arg ==
        x arg)
      [
        SMTPat
        ((BV_LEMMAS.e_ee_1__impl__to_i32x8 (BV_LEMMAS.e_ee_1__impl__from_i32x8 x
              <:
              Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32) arg)
      ]
      = admit ()


let hey lhs rhs: squash (
        Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl__to_i32x8 (montgomery_multiply lhs rhs) (mk_u64 0)
     == montgomery_multiply_spec 
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl__to_i32x8 lhs (mk_u64 0)) 
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl__to_i32x8 rhs (mk_u64 0))
    ) = _ by (
      let open FStar.Tactics in
      norm [iota; primops; delta_only [`%montgomery_multiply]; zeta];
      l_to_r [`e_ee_1__lemma_cancel_iv'];
      dump "goal"
    )
