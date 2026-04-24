module EquivImplSpec.Keccakf.Arm64

(* ================================================================
   NEON (Arm64, N=2, v_T=t_e_uint64x2_t) instantiation of the generic
   keccak_f equivalence proof.

   This module constructs the 7-field [lane_correctness] record for
   [Libcrux_sha3.Simd.Arm64.impl] using the per-lane postconditions
   declared on the 7 Keccak-critical intrinsics in
   [Libcrux_intrinsics.Arm64_extract]:

     e_vdupq_n_u64, e_veorq_u64, e_veor3q_u64, e_vrax1q_u64,
     e_vxarq_u64, e_vbcaxq_u64

   Derived theorem:
     extract_lane lc_arm64 (keccakf1600 ks).f_st l
       == keccak_f (extract_lane lc_arm64 ks.f_st l)
   ================================================================ *)

#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"

open FStar.Mul
open Core_models

module G = EquivImplSpec.Keccakf.Generic
module I = Libcrux_intrinsics.Arm64_extract

(* Bring the Arm64 typeclass instance into scope so
   t_KeccakItem t_e_uint64x2_t (mk_usize 2) resolves to
   [Libcrux_sha3.Simd.Arm64.impl]. *)
let _ =
  let open Libcrux_intrinsics.Arm64_extract in
  let open Libcrux_sha3.Traits in
  let open Libcrux_sha3.Simd.Arm64 in
  ()

(* ================================================================
   Arm64 lane extraction

   For N=2, a [t_e_uint64x2_t] has two u64 lanes; the [lane] field
   of [lane_correctness] is simply [get_lane_u64x2].
   ================================================================ *)

let arm64_lane (v: I.t_e_uint64x2_t) (l: nat{l < 2}) : u64 =
  I.get_lane_u64x2 v l

(* ================================================================
   Lane-correctness field proofs

   Each proof is a short unfolding:
     1. typeclass resolution expands [f_*] to the concrete [e_*]
        helper in [Libcrux_sha3.Simd.Arm64],
     2. that helper expands to the intrinsic in [I],
     3. the intrinsic's [ensures] clause (forall-over-lane) supplies
        the per-lane equation.
   ================================================================ *)

let arm64_lc_zero (l: nat{l < 2})
  : Lemma (arm64_lane (Libcrux_sha3.Traits.f_zero
             #I.t_e_uint64x2_t #(mk_usize 2)
             #FStar.Tactics.Typeclasses.solve ()) l == mk_u64 0)
  = ()

let arm64_lc_xor5 (a b c d e: I.t_e_uint64x2_t) (l: nat{l < 2})
  : Lemma (arm64_lane (Libcrux_sha3.Traits.f_xor5
             #I.t_e_uint64x2_t #(mk_usize 2)
             #FStar.Tactics.Typeclasses.solve a b c d e) l ==
           (((arm64_lane a l ^. arm64_lane b l) ^. arm64_lane c l)
             ^. arm64_lane d l) ^. arm64_lane e l)
  = ()

let arm64_lc_rotate_left1_and_xor (a b: I.t_e_uint64x2_t) (l: nat{l < 2})
  : Lemma (arm64_lane (Libcrux_sha3.Traits.f_rotate_left1_and_xor
             #I.t_e_uint64x2_t #(mk_usize 2)
             #FStar.Tactics.Typeclasses.solve a b) l ==
           arm64_lane a l ^.
           Core_models.Num.impl_u64__rotate_left (arm64_lane b l) (mk_u32 1))
  = ()

let arm64_lc_xor_and_rotate (v_LEFT v_RIGHT: i32) (a b: I.t_e_uint64x2_t) (l: nat{l < 2})
  : Lemma
      (requires
        ((Rust_primitives.Hax.Int.from_machine v_LEFT <: Hax_lib.Int.t_Int) +
         (Rust_primitives.Hax.Int.from_machine v_RIGHT <: Hax_lib.Int.t_Int)) =
        (Rust_primitives.Hax.Int.from_machine (mk_i32 64) <: Hax_lib.Int.t_Int) /\
        v_RIGHT >. mk_i32 0 /\
        v_RIGHT <. mk_i32 64)
      (ensures
        arm64_lane (Libcrux_sha3.Traits.f_xor_and_rotate
          #I.t_e_uint64x2_t #(mk_usize 2)
          #FStar.Tactics.Typeclasses.solve v_LEFT v_RIGHT a b) l ==
        Core_models.Num.impl_u64__rotate_left
          (arm64_lane a l ^. arm64_lane b l) (cast (v_LEFT <: i32) <: u32))
  = ()

let arm64_lc_and_not_xor (a b c: I.t_e_uint64x2_t) (l: nat{l < 2})
  : Lemma (arm64_lane (Libcrux_sha3.Traits.f_and_not_xor
             #I.t_e_uint64x2_t #(mk_usize 2)
             #FStar.Tactics.Typeclasses.solve a b c) l ==
           arm64_lane a l ^. (arm64_lane b l &. (~. (arm64_lane c l))))
  = ()

let arm64_lc_xor_constant (a: I.t_e_uint64x2_t) (c: u64) (l: nat{l < 2})
  : Lemma (arm64_lane (Libcrux_sha3.Traits.f_xor_constant
             #I.t_e_uint64x2_t #(mk_usize 2)
             #FStar.Tactics.Typeclasses.solve a c) l ==
           arm64_lane a l ^. c)
  = ()

let arm64_lc_xor (a b: I.t_e_uint64x2_t) (l: nat{l < 2})
  : Lemma (arm64_lane (Libcrux_sha3.Traits.f_xor
             #I.t_e_uint64x2_t #(mk_usize 2)
             #FStar.Tactics.Typeclasses.solve a b) l ==
           arm64_lane a l ^. arm64_lane b l)
  = ()

(* ================================================================
   Assemble the [lane_correctness] record
   ================================================================ *)

let lc_arm64 : G.lane_correctness (mk_usize 2) #I.t_e_uint64x2_t =
  {
    lane = arm64_lane;
    lc_zero = arm64_lc_zero;
    lc_xor5 = arm64_lc_xor5;
    lc_rotate_left1_and_xor = arm64_lc_rotate_left1_and_xor;
    lc_xor_and_rotate = arm64_lc_xor_and_rotate;
    lc_and_not_xor = arm64_lc_and_not_xor;
    lc_xor_constant = arm64_lc_xor_constant;
    lc_xor = arm64_lc_xor;
  }

(* ================================================================
   MAIN THEOREM: extract_lane commutes with keccakf1600 on Arm64.

   Direct specialization of [lemma_keccakf1600_to_spec].
   ================================================================ *)

let lemma_keccakf1600_arm64
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 2) I.t_e_uint64x2_t)
      (l: nat{l < 2})
  : Lemma
      (G.extract_lane (mk_usize 2) lc_arm64
         (Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 2)
            #I.t_e_uint64x2_t ks)
           .Libcrux_sha3.Generic_keccak.f_st l
       ==
       Hacspec_sha3.Keccak_f.keccak_f
         (G.extract_lane (mk_usize 2) lc_arm64
            ks.Libcrux_sha3.Generic_keccak.f_st l))
  = G.lemma_keccakf1600_to_spec (mk_usize 2) lc_arm64 ks l
