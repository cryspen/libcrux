module RmMe
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

open Libcrux_ml_dsa.Simd.Avx2.Arithmetic
open FStar.FunctionalExtensionality    

// open Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas
open Core_models.Abstractions.Bitvec.Int_vec_interp

unfold let i = mk_u64 0

// ///Lemma that asserts that applying BitVec :: < 256 > :: from and then i32x8 :: from is the identity.
// assume
// val e_ee_1__lemma_cancel_iv' (x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

//   : Lemma
//       (ensures
//         (e_ee_1__impl__to_i32x8 (e_ee_1__impl__from_i32x8 x)) ==
//         x)
//       [SMTPat (e_ee_1__impl__to_i32x8 (e_ee_1__impl__from_i32x8 x))]


// ///Lemma that asserts that applying i32x8 :: from and then BitVec :: < 256 > :: from is the identity.
// assume
// val e_ee_1__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
//   -> Lemma
//       (ensures
//         (e_ee_1__impl__from_i32x8 (e_ee_1__impl__to_i32x8 x)) == x)
//       [
//         SMTPat (e_ee_1__impl__from_i32x8 (e_ee_1__impl__to_i32x8 x))
//       ]


// ///Lemma that asserts that applying i32x8 :: from and then BitVec :: < 256 > :: from is the identity.
// assume
// val e_ee_1__lemma_cancel_bv'2: x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) -> i:(i:u64 {v i < 8})
//   -> Lemma
//       (ensures (e_ee_1__impl__from_i32x8 (e_ee_1__impl__to_i32x8 x)).[i] == x.[i])
//       [SMTPat (((e_ee_1__impl__from_i32x8 (e_ee_1__impl__to_i32x8 x)).[i]))]

open FStar.Tactics

let lemma lhs rhs (i: u64 {v i < 8}): squash (
     (e_ee_1__impl__to_i32x8 (montgomery_multiply lhs rhs)).[i]
  == (montgomery_multiply_spec
        ((e_ee_1__impl__to_i32x8 lhs).[i])
        ((e_ee_1__impl__to_i32x8 rhs).[i])
    )
) = _ by (
  norm [iota; primops; delta_only [`%montgomery_multiply]; zeta];
  l_to_r [`Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__lemma_cancel_iv]
)

// type fnarr (n: u64) (t: Type0) = i:u64 {v i < v n} ^-> t
// assume val bv: Type0

// assume val from_i32x8: fnarr (mk_u64 8) i32 -> bv
// assume val to_i32x8: bv -> fnarr (mk_u64 8) i32


// let to_from_i32x8 (x: fnarr (mk_u64 8) i32) (i: u64 {v i < 8})
//   : Lemma (to_i32x8 (from_i32x8 x) i == x i) [SMTPat (to_i32x8 (from_i32x8 x) i)]
//       = admit ()

// let to_from_i32x8' (x: fnarr (mk_u64 8) i32)
//   : Lemma (to_i32x8 (from_i32x8 x) == x) [SMTPat (to_i32x8 (from_i32x8 x))]
//       = admit ()

// assume val spec: i32 -> i32 -> i32

// module RI = Rust_primitives.Integers

// let body (lhs rhs: bv): fnarr (mk_u64 8)  =
//   (FStar.FunctionalExtensionality.on_domain (i:
//         RI.u64 { RI.v i < RI.v (RI.mk_u64 8) })
//       (fun i ->
//           match i with
//           | RI.MkInt 0 -> spec (to_i32x8 lhs (RI.mk_u64 0)) (to_i32x8 rhs (RI.mk_u64 0))
//           | RI.MkInt 1 -> spec (to_i32x8 lhs (RI.mk_u64 1)) (to_i32x8 rhs (RI.mk_u64 1))
//           | RI.MkInt 2 -> spec (to_i32x8 lhs (RI.mk_u64 2)) (to_i32x8 rhs (RI.mk_u64 2))
//           | RI.MkInt 3 -> spec (to_i32x8 lhs (RI.mk_u64 3)) (to_i32x8 rhs (RI.mk_u64 3))
//           | RI.MkInt 4 -> spec (to_i32x8 lhs (RI.mk_u64 4)) (to_i32x8 rhs (RI.mk_u64 4))
//           | RI.MkInt 5 -> spec (to_i32x8 lhs (RI.mk_u64 5)) (to_i32x8 rhs (RI.mk_u64 5))
//           | RI.MkInt 6 -> spec (to_i32x8 lhs (RI.mk_u64 6)) (to_i32x8 rhs (RI.mk_u64 6))
//           | RI.MkInt 7 -> spec (to_i32x8 lhs (RI.mk_u64 7)) (to_i32x8 rhs (RI.mk_u64 7))))

// let test (lhs rhs: bv) = from_i32x8 (body lhs rhs)

// let test_lemma (lhs rhs: bv) =
//     // to_from_i32x8 (body lhs rhs) (mk_u64 0);
//     assert (
//         to_i32x8 (test lhs rhs) (mk_u64 0)
//      == spec (to_i32x8 lhs (mk_u64 0)) (to_i32x8 rhs (mk_u64 0))
//     ) 
//     // by (
//     //   let open FStar.Tactics in
//     //   norm [iota; primops; delta_only [`%test]; zeta];
//     //   // l_to_r [`e_ee_1__lemma_cancel_iv'];
//     //   dump "goal"
//     // )
