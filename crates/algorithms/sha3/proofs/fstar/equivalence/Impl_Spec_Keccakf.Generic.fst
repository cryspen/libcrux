module Impl_Spec_Keccakf.Generic

(* ================================================================
   Generic keccak_f equivalence via lane-wise `to_spec` commutativity.

   MAIN THEOREM (lemma_keccakf1600_to_spec):

     extract_lane lc (keccakf1600 v_N #v_T ks).f_st l ==
       keccak_f (extract_lane lc ks.f_st l)

   i.e., extracting any lane from the SIMD keccakf1600 result equals
   running the scalar spec keccak_f on that lane of the input.

   ARCHITECTURE:

   1. `lane_correctness` record — 7 hypotheses any KeccakItem backend
      must satisfy (lc_xor5, lc_rotate_left1_and_xor, lc_xor_and_rotate,
      lc_and_not_xor, lc_xor_constant, lc_xor, lc_zero). These say
      that extracting a lane commutes with each typeclass operation.

   2. `extract_lane lc state l` — maps `t_Array v_T 25` to
      `t_Array u64 25` by applying `lc.lane` pointwise:
        (extract_lane state l).[i] = lc.lane state.[i] l

   3. Per-step commutativity lemmas — for each keccak step (theta+rho,
      pi, chi, iota), prove:
        extract_lane (impl_step state) l == spec_step (extract_lane state l)

   4. Composition — chain per-step commutativity into one-round, then
      induction over 24 rounds.

   PROOF STATUS:

   Proven (= ()):
   - All generic impl-side lemmas (Phase 1): lemma_theta_generic,
     lemma_rho_{0..4}_generic, lemma_pi_{0..4}_generic,
     lemma_rho_unfold_generic, lemma_pi_unfold_generic.
     These express impl results in terms of abstract KeccakItem ops.
   - Operation-level lane commutativity: lane_xor5, lane_xor, etc.
     (trivial wrappers around lane_correctness fields)
   - One-round and multi-round composition (assuming per-step lemmas)

   Admitted (need proof):
   - lemma_theta_rho_to_spec: theta+rho commutativity with extract_lane
   - lemma_pi_to_spec: pi commutativity (pure permutation, should be easy)
   - lemma_chi_to_spec: chi commutativity (needs logand_commutative)
   - lemma_iota_to_spec: iota commutativity (needs lc_xor_constant + eq_intro)

   Admitted (library-level, same as portable proof):
   - lemma_rotate_left_zero: rotate_left(x, 0) == x
   - logand_commutative: (a &. b) == (b &. a)
   - lemma_rho_offsets_values: RHO_OFFSETS array element values
   - lemma_keccakf1600_is_rounds: fold_range bridge (impl side)
   - lemma_keccak_f_is_rounds: fold_range bridge (spec side)

   PROOF STRATEGY for the to_spec admits:

   Each to_spec lemma follows the same pattern:
   1. Use the generic impl-side lemma to know what each slot contains
      (e.g., lemma_rho_0_generic says r.[1] == f_xor_and_rotate ... s.[1] d.[0])
   2. Apply lane_* helpers to convert from abstract v_T ops to scalar u64 ops
      (e.g., lane_xor_and_rotate says lc.lane(f_xor_and_rotate ... a b) l == rotl(lane a l ^. lane b l, LEFT))
   3. Use spec-side reduction (e.g., lemma_rho_theta_spec from the portable proof)
   4. Conclude with Rust_primitives.Arrays.eq_intro

   The tricky part is getting Z3 to see pointwise equality across all 25
   indices. The portable proof handles this with explicit per-index asserts;
   the generic proof needs the same but with lane extraction in between.

   INSTANTIATION (future files):
   - Portable (N=1, u64): lane(x,0) = x. All lc_* are `= ()`.
   - NEON (N=2, uint64x2_t): lane = get_lane64, lc_* from arm64_extract.rs specs
   - AVX2 (N=4, Vec256): lane = get_lane, lc_* from avx2_extract.rs specs
   ================================================================ *)

#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"

open FStar.Mul
open Core_models

let _ =
  let open Libcrux_sha3.Traits in
  let open Libcrux_sha3.Simd.Portable in
  ()

(* ================================================================
   Lane-correctness specification
   ================================================================ *)

noeq type lane_correctness
  (v_N: usize)
  (#v_T: Type0)
  {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |} = {

  lane: v_T -> l:nat{l < v v_N} -> u64;

  lc_zero: (l:nat{l < v v_N}) ->
    Lemma (lane (Libcrux_sha3.Traits.f_zero #v_T #v_N #inst ()) l == mk_u64 0);

  lc_xor5: (a:v_T) -> (b:v_T) -> (c:v_T) -> (d:v_T) -> (e:v_T) -> (l:nat{l < v v_N}) ->
    Lemma (lane (Libcrux_sha3.Traits.f_xor5 #v_T #v_N #inst a b c d e) l ==
           (((lane a l ^. lane b l) ^. lane c l) ^. lane d l) ^. lane e l);

  lc_rotate_left1_and_xor: (a:v_T) -> (b:v_T) -> (l:nat{l < v v_N}) ->
    Lemma (lane (Libcrux_sha3.Traits.f_rotate_left1_and_xor #v_T #v_N #inst a b) l ==
           lane a l ^. Core_models.Num.impl_u64__rotate_left (lane b l) (mk_u32 1));

  lc_xor_and_rotate: (v_LEFT:i32) -> (v_RIGHT:i32) -> (a:v_T) -> (b:v_T) -> (l:nat{l < v v_N}) ->
    Lemma
      (requires
        ((Rust_primitives.Hax.Int.from_machine v_LEFT <: Hax_lib.Int.t_Int) +
         (Rust_primitives.Hax.Int.from_machine v_RIGHT <: Hax_lib.Int.t_Int)) =
        (Rust_primitives.Hax.Int.from_machine (mk_i32 64) <: Hax_lib.Int.t_Int) /\
        v_RIGHT >. mk_i32 0 /\
        v_RIGHT <. mk_i32 64)
      (ensures
        lane (Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst v_LEFT v_RIGHT a b) l ==
        Core_models.Num.impl_u64__rotate_left (lane a l ^. lane b l) (cast (v_LEFT <: i32) <: u32));

  lc_and_not_xor: (a:v_T) -> (b:v_T) -> (c:v_T) -> (l:nat{l < v v_N}) ->
    Lemma (lane (Libcrux_sha3.Traits.f_and_not_xor #v_T #v_N #inst a b c) l ==
           lane a l ^. (lane b l &. (~. (lane c l))));

  lc_xor_constant: (a:v_T) -> (c:u64) -> (l:nat{l < v v_N}) ->
    Lemma (lane (Libcrux_sha3.Traits.f_xor_constant #v_T #v_N #inst a c) l ==
           lane a l ^. c);

  lc_xor: (a:v_T) -> (b:v_T) -> (l:nat{l < v v_N}) ->
    Lemma (lane (Libcrux_sha3.Traits.f_xor #v_T #v_N #inst a b) l ==
           lane a l ^. lane b l);
}

(* ================================================================
   extract_lane: maps SIMD state to a scalar spec state for lane l
   ================================================================ *)

let extract_lane
      (#v_T: Type0) (v_N: usize)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (lc: lane_correctness v_N #v_T)
      (state: t_Array v_T (mk_usize 25))
      (l: nat{l < v v_N})
  : t_Array u64 (mk_usize 25) =
  Rust_primitives.Arrays.createi (mk_usize 25) (fun i -> lc.lane state.[i] l)

(* Shorthand for the spec's state type *)
let spec_state = t_Array u64 (mk_usize 25)

(* Shorthand for the impl's state type *)
let impl_state (v_N: usize) (v_T: Type0)
  {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |} =
  Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T

(* ================================================================
   Operation-level commutativity with extract_lane

   These show that applying a KeccakItem operation to SIMD elements
   and then extracting a lane equals extracting lanes first and then
   applying the scalar operation. Each is a direct consequence of the
   corresponding lane_correctness hypothesis.
   ================================================================ *)

let lane_xor5
      (#v_T: Type0) (v_N: usize)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (lc: lane_correctness v_N #v_T)
      (a b c d e: v_T) (l: nat{l < v v_N})
  : Lemma (lc.lane (Libcrux_sha3.Traits.f_xor5 #v_T #v_N #inst a b c d e) l ==
           (((lc.lane a l ^. lc.lane b l) ^. lc.lane c l) ^. lc.lane d l) ^. lc.lane e l)
  = lc.lc_xor5 a b c d e l

let lane_rotate_left1_and_xor
      (#v_T: Type0) (v_N: usize)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (lc: lane_correctness v_N #v_T)
      (a b: v_T) (l: nat{l < v v_N})
  : Lemma (lc.lane (Libcrux_sha3.Traits.f_rotate_left1_and_xor #v_T #v_N #inst a b) l ==
           lc.lane a l ^. Core_models.Num.impl_u64__rotate_left (lc.lane b l) (mk_u32 1))
  = lc.lc_rotate_left1_and_xor a b l

let lane_xor_and_rotate
      (#v_T: Type0) (v_N: usize)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (lc: lane_correctness v_N #v_T)
      (v_LEFT v_RIGHT: i32) (a b: v_T) (l: nat{l < v v_N})
  : Lemma
      (requires
        ((Rust_primitives.Hax.Int.from_machine v_LEFT <: Hax_lib.Int.t_Int) +
         (Rust_primitives.Hax.Int.from_machine v_RIGHT <: Hax_lib.Int.t_Int)) =
        (Rust_primitives.Hax.Int.from_machine (mk_i32 64) <: Hax_lib.Int.t_Int) /\
        v_RIGHT >. mk_i32 0 /\
        v_RIGHT <. mk_i32 64)
      (ensures
        lc.lane (Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst v_LEFT v_RIGHT a b) l ==
        Core_models.Num.impl_u64__rotate_left (lc.lane a l ^. lc.lane b l) (cast (v_LEFT <: i32) <: u32))
  = lc.lc_xor_and_rotate v_LEFT v_RIGHT a b l

let lane_and_not_xor
      (#v_T: Type0) (v_N: usize)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (lc: lane_correctness v_N #v_T)
      (a b c: v_T) (l: nat{l < v v_N})
  : Lemma (lc.lane (Libcrux_sha3.Traits.f_and_not_xor #v_T #v_N #inst a b c) l ==
           lc.lane a l ^. (lc.lane b l &. (~. (lc.lane c l))))
  = lc.lc_and_not_xor a b c l

let lane_xor_constant
      (#v_T: Type0) (v_N: usize)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (lc: lane_correctness v_N #v_T)
      (a: v_T) (c: u64) (l: nat{l < v v_N})
  : Lemma (lc.lane (Libcrux_sha3.Traits.f_xor_constant #v_T #v_N #inst a c) l ==
           lc.lane a l ^. c)
  = lc.lc_xor_constant a c l

let lane_xor
      (#v_T: Type0) (v_N: usize)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (lc: lane_correctness v_N #v_T)
      (a b: v_T) (l: nat{l < v v_N})
  : Lemma (lc.lane (Libcrux_sha3.Traits.f_xor #v_T #v_N #inst a b) l ==
           lc.lane a l ^. lc.lane b l)
  = lc.lc_xor a b l

(* ================================================================
   Phase 1: Generic impl-side rho lemmas (abstract v_T)

   These capture what each array slot of the rho result contains,
   expressed in terms of abstract typeclass operations.
   They should be `= ()` because they depend only on array update
   semantics, not on the concrete type v_T.
   ================================================================ *)

(** Abbreviation for rotate_left with i32 cast. *)
let rotl (x: u64) (n: i32) : u64 =
  Core_models.Num.impl_u64__rotate_left x (cast (n <: i32) <: u32)

(** Theta: state is unchanged, d matches column parities. *)
#push-options "--z3rlimit 100"
let lemma_theta_generic
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
  : Lemma
      (let s = ks.Libcrux_sha3.Generic_keccak.f_st in
       let ks', d = Libcrux_sha3.Generic_keccak.impl_2__theta v_N #v_T ks in
       ks'.Libcrux_sha3.Generic_keccak.f_st == s /\
       d.[mk_usize 0] == Libcrux_sha3.Traits.f_rotate_left1_and_xor #v_T #v_N #inst
         (Libcrux_sha3.Traits.f_xor5 #v_T #v_N #inst s.[mk_usize 20] s.[mk_usize 21] s.[mk_usize 22] s.[mk_usize 23] s.[mk_usize 24])
         (Libcrux_sha3.Traits.f_xor5 #v_T #v_N #inst s.[mk_usize 5] s.[mk_usize 6] s.[mk_usize 7] s.[mk_usize 8] s.[mk_usize 9]) /\
       d.[mk_usize 1] == Libcrux_sha3.Traits.f_rotate_left1_and_xor #v_T #v_N #inst
         (Libcrux_sha3.Traits.f_xor5 #v_T #v_N #inst s.[mk_usize 0] s.[mk_usize 1] s.[mk_usize 2] s.[mk_usize 3] s.[mk_usize 4])
         (Libcrux_sha3.Traits.f_xor5 #v_T #v_N #inst s.[mk_usize 10] s.[mk_usize 11] s.[mk_usize 12] s.[mk_usize 13] s.[mk_usize 14]) /\
       d.[mk_usize 2] == Libcrux_sha3.Traits.f_rotate_left1_and_xor #v_T #v_N #inst
         (Libcrux_sha3.Traits.f_xor5 #v_T #v_N #inst s.[mk_usize 5] s.[mk_usize 6] s.[mk_usize 7] s.[mk_usize 8] s.[mk_usize 9])
         (Libcrux_sha3.Traits.f_xor5 #v_T #v_N #inst s.[mk_usize 15] s.[mk_usize 16] s.[mk_usize 17] s.[mk_usize 18] s.[mk_usize 19]) /\
       d.[mk_usize 3] == Libcrux_sha3.Traits.f_rotate_left1_and_xor #v_T #v_N #inst
         (Libcrux_sha3.Traits.f_xor5 #v_T #v_N #inst s.[mk_usize 10] s.[mk_usize 11] s.[mk_usize 12] s.[mk_usize 13] s.[mk_usize 14])
         (Libcrux_sha3.Traits.f_xor5 #v_T #v_N #inst s.[mk_usize 20] s.[mk_usize 21] s.[mk_usize 22] s.[mk_usize 23] s.[mk_usize 24]) /\
       d.[mk_usize 4] == Libcrux_sha3.Traits.f_rotate_left1_and_xor #v_T #v_N #inst
         (Libcrux_sha3.Traits.f_xor5 #v_T #v_N #inst s.[mk_usize 15] s.[mk_usize 16] s.[mk_usize 17] s.[mk_usize 18] s.[mk_usize 19])
         (Libcrux_sha3.Traits.f_xor5 #v_T #v_N #inst s.[mk_usize 0] s.[mk_usize 1] s.[mk_usize 2] s.[mk_usize 3] s.[mk_usize 4]))
  = ()
#pop-options

(** rho_0_: sets column 0, preserves columns 1-4.
    Column 0 uses f_xor at index 0, f_xor_and_rotate at indices 1-4. *)
#push-options "--z3rlimit 200"
let lemma_rho_0_generic
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (d: t_Array v_T (mk_usize 5))
  : Lemma
      (let s = ks.Libcrux_sha3.Generic_keccak.f_st in
       let r = (Libcrux_sha3.Generic_keccak.impl_2__rho_0_ v_N #v_T ks d)
                .Libcrux_sha3.Generic_keccak.f_st in
       r.[mk_usize 0] == Libcrux_sha3.Traits.f_xor #v_T #v_N #inst s.[mk_usize 0] d.[mk_usize 0] /\
       r.[mk_usize 1] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 36) (mk_i32 28) s.[mk_usize 1] d.[mk_usize 0] /\
       r.[mk_usize 2] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 3) (mk_i32 61) s.[mk_usize 2] d.[mk_usize 0] /\
       r.[mk_usize 3] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 41) (mk_i32 23) s.[mk_usize 3] d.[mk_usize 0] /\
       r.[mk_usize 4] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 18) (mk_i32 46) s.[mk_usize 4] d.[mk_usize 0] /\
       r.[mk_usize 5] == s.[mk_usize 5] /\ r.[mk_usize 6] == s.[mk_usize 6] /\
       r.[mk_usize 7] == s.[mk_usize 7] /\ r.[mk_usize 8] == s.[mk_usize 8] /\
       r.[mk_usize 9] == s.[mk_usize 9] /\ r.[mk_usize 10] == s.[mk_usize 10] /\
       r.[mk_usize 11] == s.[mk_usize 11] /\ r.[mk_usize 12] == s.[mk_usize 12] /\
       r.[mk_usize 13] == s.[mk_usize 13] /\ r.[mk_usize 14] == s.[mk_usize 14] /\
       r.[mk_usize 15] == s.[mk_usize 15] /\ r.[mk_usize 16] == s.[mk_usize 16] /\
       r.[mk_usize 17] == s.[mk_usize 17] /\ r.[mk_usize 18] == s.[mk_usize 18] /\
       r.[mk_usize 19] == s.[mk_usize 19] /\ r.[mk_usize 20] == s.[mk_usize 20] /\
       r.[mk_usize 21] == s.[mk_usize 21] /\ r.[mk_usize 22] == s.[mk_usize 22] /\
       r.[mk_usize 23] == s.[mk_usize 23] /\ r.[mk_usize 24] == s.[mk_usize 24])
  = ()
#pop-options

#push-options "--z3rlimit 200"
let lemma_rho_1_generic
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (d: t_Array v_T (mk_usize 5))
  : Lemma
      (let s = ks.Libcrux_sha3.Generic_keccak.f_st in
       let r = (Libcrux_sha3.Generic_keccak.impl_2__rho_1_ v_N #v_T ks d)
                .Libcrux_sha3.Generic_keccak.f_st in
       r.[mk_usize 0] == s.[mk_usize 0] /\ r.[mk_usize 1] == s.[mk_usize 1] /\
       r.[mk_usize 2] == s.[mk_usize 2] /\ r.[mk_usize 3] == s.[mk_usize 3] /\
       r.[mk_usize 4] == s.[mk_usize 4] /\
       r.[mk_usize 5] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 1) (mk_i32 63) s.[mk_usize 5] d.[mk_usize 1] /\
       r.[mk_usize 6] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 44) (mk_i32 20) s.[mk_usize 6] d.[mk_usize 1] /\
       r.[mk_usize 7] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 10) (mk_i32 54) s.[mk_usize 7] d.[mk_usize 1] /\
       r.[mk_usize 8] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 45) (mk_i32 19) s.[mk_usize 8] d.[mk_usize 1] /\
       r.[mk_usize 9] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 2) (mk_i32 62) s.[mk_usize 9] d.[mk_usize 1] /\
       r.[mk_usize 10] == s.[mk_usize 10] /\ r.[mk_usize 11] == s.[mk_usize 11] /\
       r.[mk_usize 12] == s.[mk_usize 12] /\ r.[mk_usize 13] == s.[mk_usize 13] /\
       r.[mk_usize 14] == s.[mk_usize 14] /\ r.[mk_usize 15] == s.[mk_usize 15] /\
       r.[mk_usize 16] == s.[mk_usize 16] /\ r.[mk_usize 17] == s.[mk_usize 17] /\
       r.[mk_usize 18] == s.[mk_usize 18] /\ r.[mk_usize 19] == s.[mk_usize 19] /\
       r.[mk_usize 20] == s.[mk_usize 20] /\ r.[mk_usize 21] == s.[mk_usize 21] /\
       r.[mk_usize 22] == s.[mk_usize 22] /\ r.[mk_usize 23] == s.[mk_usize 23] /\
       r.[mk_usize 24] == s.[mk_usize 24])
  = ()
#pop-options

#push-options "--z3rlimit 200"
let lemma_rho_2_generic
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (d: t_Array v_T (mk_usize 5))
  : Lemma
      (let s = ks.Libcrux_sha3.Generic_keccak.f_st in
       let r = (Libcrux_sha3.Generic_keccak.impl_2__rho_2_ v_N #v_T ks d)
                .Libcrux_sha3.Generic_keccak.f_st in
       r.[mk_usize 0] == s.[mk_usize 0] /\ r.[mk_usize 1] == s.[mk_usize 1] /\
       r.[mk_usize 2] == s.[mk_usize 2] /\ r.[mk_usize 3] == s.[mk_usize 3] /\
       r.[mk_usize 4] == s.[mk_usize 4] /\ r.[mk_usize 5] == s.[mk_usize 5] /\
       r.[mk_usize 6] == s.[mk_usize 6] /\ r.[mk_usize 7] == s.[mk_usize 7] /\
       r.[mk_usize 8] == s.[mk_usize 8] /\ r.[mk_usize 9] == s.[mk_usize 9] /\
       r.[mk_usize 10] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 62) (mk_i32 2) s.[mk_usize 10] d.[mk_usize 2] /\
       r.[mk_usize 11] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 6) (mk_i32 58) s.[mk_usize 11] d.[mk_usize 2] /\
       r.[mk_usize 12] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 43) (mk_i32 21) s.[mk_usize 12] d.[mk_usize 2] /\
       r.[mk_usize 13] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 15) (mk_i32 49) s.[mk_usize 13] d.[mk_usize 2] /\
       r.[mk_usize 14] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 61) (mk_i32 3) s.[mk_usize 14] d.[mk_usize 2] /\
       r.[mk_usize 15] == s.[mk_usize 15] /\ r.[mk_usize 16] == s.[mk_usize 16] /\
       r.[mk_usize 17] == s.[mk_usize 17] /\ r.[mk_usize 18] == s.[mk_usize 18] /\
       r.[mk_usize 19] == s.[mk_usize 19] /\ r.[mk_usize 20] == s.[mk_usize 20] /\
       r.[mk_usize 21] == s.[mk_usize 21] /\ r.[mk_usize 22] == s.[mk_usize 22] /\
       r.[mk_usize 23] == s.[mk_usize 23] /\ r.[mk_usize 24] == s.[mk_usize 24])
  = ()
#pop-options

#push-options "--z3rlimit 200"
let lemma_rho_3_generic
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (d: t_Array v_T (mk_usize 5))
  : Lemma
      (let s = ks.Libcrux_sha3.Generic_keccak.f_st in
       let r = (Libcrux_sha3.Generic_keccak.impl_2__rho_3_ v_N #v_T ks d)
                .Libcrux_sha3.Generic_keccak.f_st in
       r.[mk_usize 0] == s.[mk_usize 0] /\ r.[mk_usize 1] == s.[mk_usize 1] /\
       r.[mk_usize 2] == s.[mk_usize 2] /\ r.[mk_usize 3] == s.[mk_usize 3] /\
       r.[mk_usize 4] == s.[mk_usize 4] /\ r.[mk_usize 5] == s.[mk_usize 5] /\
       r.[mk_usize 6] == s.[mk_usize 6] /\ r.[mk_usize 7] == s.[mk_usize 7] /\
       r.[mk_usize 8] == s.[mk_usize 8] /\ r.[mk_usize 9] == s.[mk_usize 9] /\
       r.[mk_usize 10] == s.[mk_usize 10] /\ r.[mk_usize 11] == s.[mk_usize 11] /\
       r.[mk_usize 12] == s.[mk_usize 12] /\ r.[mk_usize 13] == s.[mk_usize 13] /\
       r.[mk_usize 14] == s.[mk_usize 14] /\
       r.[mk_usize 15] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 28) (mk_i32 36) s.[mk_usize 15] d.[mk_usize 3] /\
       r.[mk_usize 16] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 55) (mk_i32 9) s.[mk_usize 16] d.[mk_usize 3] /\
       r.[mk_usize 17] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 25) (mk_i32 39) s.[mk_usize 17] d.[mk_usize 3] /\
       r.[mk_usize 18] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 21) (mk_i32 43) s.[mk_usize 18] d.[mk_usize 3] /\
       r.[mk_usize 19] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 56) (mk_i32 8) s.[mk_usize 19] d.[mk_usize 3] /\
       r.[mk_usize 20] == s.[mk_usize 20] /\ r.[mk_usize 21] == s.[mk_usize 21] /\
       r.[mk_usize 22] == s.[mk_usize 22] /\ r.[mk_usize 23] == s.[mk_usize 23] /\
       r.[mk_usize 24] == s.[mk_usize 24])
  = ()
#pop-options

#push-options "--z3rlimit 200"
let lemma_rho_4_generic
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (d: t_Array v_T (mk_usize 5))
  : Lemma
      (let s = ks.Libcrux_sha3.Generic_keccak.f_st in
       let r = (Libcrux_sha3.Generic_keccak.impl_2__rho_4_ v_N #v_T ks d)
                .Libcrux_sha3.Generic_keccak.f_st in
       r.[mk_usize 0] == s.[mk_usize 0] /\ r.[mk_usize 1] == s.[mk_usize 1] /\
       r.[mk_usize 2] == s.[mk_usize 2] /\ r.[mk_usize 3] == s.[mk_usize 3] /\
       r.[mk_usize 4] == s.[mk_usize 4] /\ r.[mk_usize 5] == s.[mk_usize 5] /\
       r.[mk_usize 6] == s.[mk_usize 6] /\ r.[mk_usize 7] == s.[mk_usize 7] /\
       r.[mk_usize 8] == s.[mk_usize 8] /\ r.[mk_usize 9] == s.[mk_usize 9] /\
       r.[mk_usize 10] == s.[mk_usize 10] /\ r.[mk_usize 11] == s.[mk_usize 11] /\
       r.[mk_usize 12] == s.[mk_usize 12] /\ r.[mk_usize 13] == s.[mk_usize 13] /\
       r.[mk_usize 14] == s.[mk_usize 14] /\ r.[mk_usize 15] == s.[mk_usize 15] /\
       r.[mk_usize 16] == s.[mk_usize 16] /\ r.[mk_usize 17] == s.[mk_usize 17] /\
       r.[mk_usize 18] == s.[mk_usize 18] /\ r.[mk_usize 19] == s.[mk_usize 19] /\
       r.[mk_usize 20] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 27) (mk_i32 37) s.[mk_usize 20] d.[mk_usize 4] /\
       r.[mk_usize 21] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 20) (mk_i32 44) s.[mk_usize 21] d.[mk_usize 4] /\
       r.[mk_usize 22] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 39) (mk_i32 25) s.[mk_usize 22] d.[mk_usize 4] /\
       r.[mk_usize 23] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 8) (mk_i32 56) s.[mk_usize 23] d.[mk_usize 4] /\
       r.[mk_usize 24] == Libcrux_sha3.Traits.f_xor_and_rotate #v_T #v_N #inst (mk_i32 14) (mk_i32 50) s.[mk_usize 24] d.[mk_usize 4])
  = ()
#pop-options

(** rho unfolds to rho_0_ through rho_4_ chain. *)
#push-options "--z3rlimit 100"
let lemma_rho_unfold_generic
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (d: t_Array v_T (mk_usize 5))
  : Lemma
      (let open Libcrux_sha3.Generic_keccak in
       impl_2__rho v_N #v_T ks d ==
       (let ks0 = impl_2__rho_0_ v_N #v_T ks d in
        let ks1 = impl_2__rho_1_ v_N #v_T ks0 d in
        let ks2 = impl_2__rho_2_ v_N #v_T ks1 d in
        let ks3 = impl_2__rho_3_ v_N #v_T ks2 d in
        impl_2__rho_4_ v_N #v_T ks3 d))
  = ()
#pop-options

(* ================================================================
   Phase 1b: Generic impl-side pi lemmas (abstract v_T)
   ================================================================ *)

#push-options "--z3rlimit 200"
let lemma_pi_0_generic
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (ks old: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
  : Lemma
      (let s = ks.Libcrux_sha3.Generic_keccak.f_st in
       let o = old.Libcrux_sha3.Generic_keccak.f_st in
       let r = (Libcrux_sha3.Generic_keccak.impl_2__pi_0_ v_N #v_T ks old)
                .Libcrux_sha3.Generic_keccak.f_st in
       r.[mk_usize 0] == s.[mk_usize 0] /\
       r.[mk_usize 1] == o.[mk_usize 15] /\
       r.[mk_usize 2] == o.[mk_usize 5] /\
       r.[mk_usize 3] == o.[mk_usize 20] /\
       r.[mk_usize 4] == o.[mk_usize 10] /\
       r.[mk_usize 5] == s.[mk_usize 5] /\ r.[mk_usize 6] == s.[mk_usize 6] /\
       r.[mk_usize 7] == s.[mk_usize 7] /\ r.[mk_usize 8] == s.[mk_usize 8] /\
       r.[mk_usize 9] == s.[mk_usize 9] /\ r.[mk_usize 10] == s.[mk_usize 10] /\
       r.[mk_usize 11] == s.[mk_usize 11] /\ r.[mk_usize 12] == s.[mk_usize 12] /\
       r.[mk_usize 13] == s.[mk_usize 13] /\ r.[mk_usize 14] == s.[mk_usize 14] /\
       r.[mk_usize 15] == s.[mk_usize 15] /\ r.[mk_usize 16] == s.[mk_usize 16] /\
       r.[mk_usize 17] == s.[mk_usize 17] /\ r.[mk_usize 18] == s.[mk_usize 18] /\
       r.[mk_usize 19] == s.[mk_usize 19] /\ r.[mk_usize 20] == s.[mk_usize 20] /\
       r.[mk_usize 21] == s.[mk_usize 21] /\ r.[mk_usize 22] == s.[mk_usize 22] /\
       r.[mk_usize 23] == s.[mk_usize 23] /\ r.[mk_usize 24] == s.[mk_usize 24])
  = ()
#pop-options

#push-options "--z3rlimit 200"
let lemma_pi_1_generic
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (ks old: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
  : Lemma
      (let s = ks.Libcrux_sha3.Generic_keccak.f_st in
       let o = old.Libcrux_sha3.Generic_keccak.f_st in
       let r = (Libcrux_sha3.Generic_keccak.impl_2__pi_1_ v_N #v_T ks old)
                .Libcrux_sha3.Generic_keccak.f_st in
       r.[mk_usize 0] == s.[mk_usize 0] /\ r.[mk_usize 1] == s.[mk_usize 1] /\
       r.[mk_usize 2] == s.[mk_usize 2] /\ r.[mk_usize 3] == s.[mk_usize 3] /\
       r.[mk_usize 4] == s.[mk_usize 4] /\
       r.[mk_usize 5] == o.[mk_usize 6] /\
       r.[mk_usize 6] == o.[mk_usize 21] /\
       r.[mk_usize 7] == o.[mk_usize 11] /\
       r.[mk_usize 8] == o.[mk_usize 1] /\
       r.[mk_usize 9] == o.[mk_usize 16] /\
       r.[mk_usize 10] == s.[mk_usize 10] /\ r.[mk_usize 11] == s.[mk_usize 11] /\
       r.[mk_usize 12] == s.[mk_usize 12] /\ r.[mk_usize 13] == s.[mk_usize 13] /\
       r.[mk_usize 14] == s.[mk_usize 14] /\ r.[mk_usize 15] == s.[mk_usize 15] /\
       r.[mk_usize 16] == s.[mk_usize 16] /\ r.[mk_usize 17] == s.[mk_usize 17] /\
       r.[mk_usize 18] == s.[mk_usize 18] /\ r.[mk_usize 19] == s.[mk_usize 19] /\
       r.[mk_usize 20] == s.[mk_usize 20] /\ r.[mk_usize 21] == s.[mk_usize 21] /\
       r.[mk_usize 22] == s.[mk_usize 22] /\ r.[mk_usize 23] == s.[mk_usize 23] /\
       r.[mk_usize 24] == s.[mk_usize 24])
  = ()
#pop-options

#push-options "--z3rlimit 200"
let lemma_pi_2_generic
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (ks old: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
  : Lemma
      (let s = ks.Libcrux_sha3.Generic_keccak.f_st in
       let o = old.Libcrux_sha3.Generic_keccak.f_st in
       let r = (Libcrux_sha3.Generic_keccak.impl_2__pi_2_ v_N #v_T ks old)
                .Libcrux_sha3.Generic_keccak.f_st in
       r.[mk_usize 0] == s.[mk_usize 0] /\ r.[mk_usize 1] == s.[mk_usize 1] /\
       r.[mk_usize 2] == s.[mk_usize 2] /\ r.[mk_usize 3] == s.[mk_usize 3] /\
       r.[mk_usize 4] == s.[mk_usize 4] /\ r.[mk_usize 5] == s.[mk_usize 5] /\
       r.[mk_usize 6] == s.[mk_usize 6] /\ r.[mk_usize 7] == s.[mk_usize 7] /\
       r.[mk_usize 8] == s.[mk_usize 8] /\ r.[mk_usize 9] == s.[mk_usize 9] /\
       r.[mk_usize 10] == o.[mk_usize 12] /\
       r.[mk_usize 11] == o.[mk_usize 2] /\
       r.[mk_usize 12] == o.[mk_usize 17] /\
       r.[mk_usize 13] == o.[mk_usize 7] /\
       r.[mk_usize 14] == o.[mk_usize 22] /\
       r.[mk_usize 15] == s.[mk_usize 15] /\ r.[mk_usize 16] == s.[mk_usize 16] /\
       r.[mk_usize 17] == s.[mk_usize 17] /\ r.[mk_usize 18] == s.[mk_usize 18] /\
       r.[mk_usize 19] == s.[mk_usize 19] /\ r.[mk_usize 20] == s.[mk_usize 20] /\
       r.[mk_usize 21] == s.[mk_usize 21] /\ r.[mk_usize 22] == s.[mk_usize 22] /\
       r.[mk_usize 23] == s.[mk_usize 23] /\ r.[mk_usize 24] == s.[mk_usize 24])
  = ()
#pop-options

#push-options "--z3rlimit 200"
let lemma_pi_3_generic
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (ks old: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
  : Lemma
      (let s = ks.Libcrux_sha3.Generic_keccak.f_st in
       let o = old.Libcrux_sha3.Generic_keccak.f_st in
       let r = (Libcrux_sha3.Generic_keccak.impl_2__pi_3_ v_N #v_T ks old)
                .Libcrux_sha3.Generic_keccak.f_st in
       r.[mk_usize 0] == s.[mk_usize 0] /\ r.[mk_usize 1] == s.[mk_usize 1] /\
       r.[mk_usize 2] == s.[mk_usize 2] /\ r.[mk_usize 3] == s.[mk_usize 3] /\
       r.[mk_usize 4] == s.[mk_usize 4] /\ r.[mk_usize 5] == s.[mk_usize 5] /\
       r.[mk_usize 6] == s.[mk_usize 6] /\ r.[mk_usize 7] == s.[mk_usize 7] /\
       r.[mk_usize 8] == s.[mk_usize 8] /\ r.[mk_usize 9] == s.[mk_usize 9] /\
       r.[mk_usize 10] == s.[mk_usize 10] /\ r.[mk_usize 11] == s.[mk_usize 11] /\
       r.[mk_usize 12] == s.[mk_usize 12] /\ r.[mk_usize 13] == s.[mk_usize 13] /\
       r.[mk_usize 14] == s.[mk_usize 14] /\
       r.[mk_usize 15] == o.[mk_usize 18] /\
       r.[mk_usize 16] == o.[mk_usize 8] /\
       r.[mk_usize 17] == o.[mk_usize 23] /\
       r.[mk_usize 18] == o.[mk_usize 13] /\
       r.[mk_usize 19] == o.[mk_usize 3] /\
       r.[mk_usize 20] == s.[mk_usize 20] /\ r.[mk_usize 21] == s.[mk_usize 21] /\
       r.[mk_usize 22] == s.[mk_usize 22] /\ r.[mk_usize 23] == s.[mk_usize 23] /\
       r.[mk_usize 24] == s.[mk_usize 24])
  = ()
#pop-options

#push-options "--z3rlimit 200"
let lemma_pi_4_generic
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (ks old: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
  : Lemma
      (let s = ks.Libcrux_sha3.Generic_keccak.f_st in
       let o = old.Libcrux_sha3.Generic_keccak.f_st in
       let r = (Libcrux_sha3.Generic_keccak.impl_2__pi_4_ v_N #v_T ks old)
                .Libcrux_sha3.Generic_keccak.f_st in
       r.[mk_usize 0] == s.[mk_usize 0] /\ r.[mk_usize 1] == s.[mk_usize 1] /\
       r.[mk_usize 2] == s.[mk_usize 2] /\ r.[mk_usize 3] == s.[mk_usize 3] /\
       r.[mk_usize 4] == s.[mk_usize 4] /\ r.[mk_usize 5] == s.[mk_usize 5] /\
       r.[mk_usize 6] == s.[mk_usize 6] /\ r.[mk_usize 7] == s.[mk_usize 7] /\
       r.[mk_usize 8] == s.[mk_usize 8] /\ r.[mk_usize 9] == s.[mk_usize 9] /\
       r.[mk_usize 10] == s.[mk_usize 10] /\ r.[mk_usize 11] == s.[mk_usize 11] /\
       r.[mk_usize 12] == s.[mk_usize 12] /\ r.[mk_usize 13] == s.[mk_usize 13] /\
       r.[mk_usize 14] == s.[mk_usize 14] /\ r.[mk_usize 15] == s.[mk_usize 15] /\
       r.[mk_usize 16] == s.[mk_usize 16] /\ r.[mk_usize 17] == s.[mk_usize 17] /\
       r.[mk_usize 18] == s.[mk_usize 18] /\ r.[mk_usize 19] == s.[mk_usize 19] /\
       r.[mk_usize 20] == o.[mk_usize 24] /\
       r.[mk_usize 21] == o.[mk_usize 14] /\
       r.[mk_usize 22] == o.[mk_usize 4] /\
       r.[mk_usize 23] == o.[mk_usize 19] /\
       r.[mk_usize 24] == o.[mk_usize 9])
  = ()
#pop-options

(** pi unfolds to pi_0_ through pi_4_ chain. *)
#push-options "--z3rlimit 100"
let lemma_pi_unfold_generic
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
  : Lemma
      (let open Libcrux_sha3.Generic_keccak in
       impl_2__pi v_N #v_T ks ==
       (let old = ks in
        let ks0 = impl_2__pi_0_ v_N #v_T ks old in
        let ks1 = impl_2__pi_1_ v_N #v_T ks0 old in
        let ks2 = impl_2__pi_2_ v_N #v_T ks1 old in
        let ks3 = impl_2__pi_3_ v_N #v_T ks2 old in
        impl_2__pi_4_ v_N #v_T ks3 old))
  = ()
#pop-options

(* ================================================================
   Phase 2: Spec-side helpers (reused from the portable proof)
   ================================================================ *)

let spec_c (state: spec_state) (x: usize{x <. mk_usize 5}) : u64 =
  ((((Hacspec_sha3.Keccak_f.get state x (mk_usize 0)) ^.
     (Hacspec_sha3.Keccak_f.get state x (mk_usize 1))) ^.
    (Hacspec_sha3.Keccak_f.get state x (mk_usize 2))) ^.
   (Hacspec_sha3.Keccak_f.get state x (mk_usize 3))) ^.
  (Hacspec_sha3.Keccak_f.get state x (mk_usize 4))

let spec_d (state: spec_state) (x: usize{x <. mk_usize 5}) : u64 =
  (spec_c state ((x +! mk_usize 4) %! mk_usize 5)) ^.
  (Core_models.Num.impl_u64__rotate_left
    (spec_c state ((x +! mk_usize 1) %! mk_usize 5))
    (mk_u32 1))

let lemma_rotate_left_zero (x: u64)
  : Lemma (Core_models.Num.impl_u64__rotate_left x (mk_u32 0) == x)
  = admit ()

let logand_commutative (#t: Rust_primitives.Integers.inttype) (a b: Rust_primitives.Integers.int_t t)
  : Lemma ((a &. b) == (b &. a))
  = admit ()

(* ================================================================
   Phase 3: to_spec commutativity — theta+rho

   Goal: extract_lane lc (theta_rho impl_state) l == rho(theta(extract_lane lc impl_state l))

   Strategy:
   1. Use generic rho lemmas to know what each slot of the impl result
      contains (in terms of abstract v_T typeclass ops)
   2. Apply lane-correctness to convert to scalar u64 ops
   3. Match against spec rho(theta(...))
   ================================================================ *)

(** Spec-side: RHO_OFFSETS values. *)
#push-options "--z3rlimit 200 --fuel 2 --ifuel 2 --split_queries always"
let lemma_rho_offsets_values (_: unit)
  : Lemma (
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 0] == mk_u32 0 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 1] == mk_u32 36 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 2] == mk_u32 3 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 3] == mk_u32 41 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 4] == mk_u32 18 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 5] == mk_u32 1 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 6] == mk_u32 44 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 7] == mk_u32 10 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 8] == mk_u32 45 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 9] == mk_u32 2 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 10] == mk_u32 62 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 11] == mk_u32 6 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 12] == mk_u32 43 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 13] == mk_u32 15 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 14] == mk_u32 61 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 15] == mk_u32 28 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 16] == mk_u32 55 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 17] == mk_u32 25 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 18] == mk_u32 21 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 19] == mk_u32 56 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 20] == mk_u32 27 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 21] == mk_u32 20 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 22] == mk_u32 39 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 23] == mk_u32 8 /\
  Hacspec_sha3.Keccak_f.v_RHO_OFFSETS.[mk_usize 24] == mk_u32 14)
  = admit()
#pop-options

(** Round constants equivalence. *)
#push-options "--z3rlimit 200"
let lemma_round_constants_equal (i: usize)
  : Lemma (requires i <. mk_usize 24)
          (ensures  Libcrux_sha3.Generic_keccak.Constants.v_ROUNDCONSTANTS.[i] ==
                    Hacspec_sha3.Keccak_f.v_ROUND_CONSTANTS.[i])
  = assert_norm (Libcrux_sha3.Generic_keccak.Constants.v_ROUNDCONSTANTS ==
                 Hacspec_sha3.Keccak_f.v_ROUND_CONSTANTS)
#pop-options

(* ================================================================
   Phase 4: to_spec commutativity for each step

   Core lemmas: extract_lane after impl step == spec step after extract_lane
   ================================================================ *)

(** Theta+Rho commutativity:
    extract_lane lc (rho(theta(ks))).f_st l == rho(theta(extract_lane lc ks.f_st l))

    TODO: This is the most complex step — needs all 25 indices.
    Start with sorry and fill in. *)

#push-options "--z3rlimit 400 --split_queries always"
let lemma_theta_rho_to_spec
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (lc: lane_correctness v_N #v_T)
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (l: nat{l < v v_N})
  : Lemma
      (let s = ks.Libcrux_sha3.Generic_keccak.f_st in
       let ks', d = Libcrux_sha3.Generic_keccak.impl_2__theta v_N #v_T ks in
       let ks'' = Libcrux_sha3.Generic_keccak.impl_2__rho v_N #v_T ks' d in
       extract_lane v_N lc ks''.Libcrux_sha3.Generic_keccak.f_st l ==
       Hacspec_sha3.Keccak_f.rho (Hacspec_sha3.Keccak_f.theta (extract_lane v_N lc s l)))
  = admit ()
#pop-options

(** Pi commutativity:
    extract_lane lc (pi(ks)).f_st l == pi(extract_lane lc ks.f_st l)

    Pi is a pure permutation — it just moves array elements around.
    Since extract_lane reads lc.lane state.[i] l, and pi permutes
    the array indices, the lane extraction commutes trivially. *)

#push-options "--z3rlimit 400 --split_queries always"
let lemma_pi_to_spec
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (lc: lane_correctness v_N #v_T)
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (l: nat{l < v v_N})
  : Lemma
      (extract_lane v_N lc
        (Libcrux_sha3.Generic_keccak.impl_2__pi v_N #v_T ks)
          .Libcrux_sha3.Generic_keccak.f_st l ==
       Hacspec_sha3.Keccak_f.pi (extract_lane v_N lc ks.Libcrux_sha3.Generic_keccak.f_st l))
  = admit ()
#pop-options

(** Chi commutativity:
    extract_lane lc (chi(ks)).f_st l == chi(extract_lane lc ks.f_st l)

    Uses lc_and_not_xor + logand_commutative. *)

#push-options "--z3rlimit 400 --split_queries always"
let lemma_chi_to_spec
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (lc: lane_correctness v_N #v_T)
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (l: nat{l < v v_N})
  : Lemma
      (extract_lane v_N lc
        (Libcrux_sha3.Generic_keccak.impl_2__chi v_N #v_T ks)
          .Libcrux_sha3.Generic_keccak.f_st l ==
       Hacspec_sha3.Keccak_f.chi (extract_lane v_N lc ks.Libcrux_sha3.Generic_keccak.f_st l))
  = admit ()
#pop-options

(** Iota commutativity:
    extract_lane lc (iota(ks, round)).f_st l == iota(extract_lane lc ks.f_st l, round)

    Uses lc_xor_constant. *)

#push-options "--z3rlimit 200"
let lemma_iota_to_spec
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (lc: lane_correctness v_N #v_T)
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (round: usize)
      (l: nat{l < v v_N})
  : Lemma
      (requires round <. mk_usize 24)
      (ensures
        extract_lane v_N lc
          (Libcrux_sha3.Generic_keccak.impl_2__iota v_N #v_T ks round)
            .Libcrux_sha3.Generic_keccak.f_st l ==
        Hacspec_sha3.Keccak_f.iota (extract_lane v_N lc ks.Libcrux_sha3.Generic_keccak.f_st l) round)
  = admit ()
#pop-options

(* ================================================================
   Phase 5: One-round and full keccakf1600 commutativity
   ================================================================ *)

let impl_one_round
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (i: usize)
  : Pure (Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (requires i <. mk_usize 24) (fun _ -> True) =
  let open Libcrux_sha3.Generic_keccak in
  let tmp0, t = impl_2__theta v_N #v_T ks in
  let ks1 = impl_2__rho v_N #v_T tmp0 t in
  let ks2 = impl_2__pi v_N #v_T ks1 in
  let ks3 = impl_2__chi v_N #v_T ks2 in
  impl_2__iota v_N #v_T ks3 i

let spec_one_round (state: spec_state) (i: usize)
  : Pure spec_state (requires i <. mk_usize 24) (fun _ -> True) =
  Hacspec_sha3.Keccak_f.iota
    (Hacspec_sha3.Keccak_f.chi
      (Hacspec_sha3.Keccak_f.pi
        (Hacspec_sha3.Keccak_f.rho
          (Hacspec_sha3.Keccak_f.theta state))))
    i

(** One-round commutativity: composition of per-step commutativity. *)
#push-options "--z3rlimit 200"
let lemma_one_round_to_spec
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (lc: lane_correctness v_N #v_T)
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (round: usize)
      (l: nat{l < v v_N})
  : Lemma
      (requires round <. mk_usize 24)
      (ensures
        extract_lane v_N lc (impl_one_round v_N ks round)
          .Libcrux_sha3.Generic_keccak.f_st l ==
        spec_one_round (extract_lane v_N lc ks.Libcrux_sha3.Generic_keccak.f_st l) round)
  = let open Libcrux_sha3.Generic_keccak in
    let s = ks.f_st in
    let ks', d = impl_2__theta v_N #v_T ks in
    let ks1 = impl_2__rho v_N #v_T ks' d in
    lemma_theta_rho_to_spec v_N lc ks l;
    let spec_after_rho = Hacspec_sha3.Keccak_f.rho (Hacspec_sha3.Keccak_f.theta (extract_lane v_N lc s l)) in
    assert (extract_lane v_N lc ks1.f_st l == spec_after_rho);
    let ks2 = impl_2__pi v_N #v_T ks1 in
    lemma_pi_to_spec v_N lc ks1 l;
    let spec_after_pi = Hacspec_sha3.Keccak_f.pi spec_after_rho in
    assert (extract_lane v_N lc ks2.f_st l == spec_after_pi);
    let ks3 = impl_2__chi v_N #v_T ks2 in
    lemma_chi_to_spec v_N lc ks2 l;
    let spec_after_chi = Hacspec_sha3.Keccak_f.chi spec_after_pi in
    assert (extract_lane v_N lc ks3.f_st l == spec_after_chi);
    lemma_iota_to_spec v_N lc ks3 round l
#pop-options

(** Recursive helpers for multi-round iteration. *)
let rec impl_rounds
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (r: usize)
  : Pure (Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (requires r <=. mk_usize 24) (fun _ -> True)
      (decreases (v (mk_usize 24) - v r)) =
  if r =. mk_usize 24 then ks
  else impl_rounds v_N (impl_one_round v_N ks r) (r +! mk_usize 1)

let rec spec_rounds (state: spec_state) (r: usize)
  : Pure spec_state
      (requires r <=. mk_usize 24) (fun _ -> True)
      (decreases (v (mk_usize 24) - v r)) =
  if r =. mk_usize 24 then state
  else spec_rounds (spec_one_round state r) (r +! mk_usize 1)

(** Induction: impl_rounds and spec_rounds commute with extract_lane. *)
#push-options "--fuel 1 --z3rlimit 200"
let rec lemma_rounds_to_spec
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (lc: lane_correctness v_N #v_T)
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (r: usize)
      (l: nat{l < v v_N})
  : Lemma
      (requires r <=. mk_usize 24)
      (ensures
        extract_lane v_N lc (impl_rounds v_N ks r).Libcrux_sha3.Generic_keccak.f_st l ==
        spec_rounds (extract_lane v_N lc ks.Libcrux_sha3.Generic_keccak.f_st l) r)
      (decreases (v (mk_usize 24) - v r))
  = if r =. mk_usize 24 then ()
    else begin
      lemma_one_round_to_spec v_N lc ks r l;
      lemma_rounds_to_spec v_N lc (impl_one_round v_N ks r) (r +! mk_usize 1) l
    end
#pop-options

(** Bridge lemmas: keccakf1600 == impl_rounds, keccak_f == spec_rounds. *)
let lemma_keccakf1600_is_rounds
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
  : Lemma (Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 v_N #v_T ks ==
           impl_rounds v_N ks (mk_usize 0))
  = admit ()

let lemma_keccak_f_is_rounds (state: spec_state)
  : Lemma (Hacspec_sha3.Keccak_f.keccak_f state ==
           spec_rounds state (mk_usize 0))
  = admit ()

(* ================================================================
   MAIN THEOREM: Generic keccak_f lane-wise equivalence.

   For any KeccakItem implementation satisfying lane_correctness,
   extracting lane l from keccakf1600 equals running the scalar
   keccak_f on lane l of the input.
   ================================================================ *)

let lemma_keccakf1600_to_spec
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (lc: lane_correctness v_N #v_T)
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (l: nat{l < v v_N})
  : Lemma
      (extract_lane v_N lc
        (Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 v_N #v_T ks)
          .Libcrux_sha3.Generic_keccak.f_st l ==
       Hacspec_sha3.Keccak_f.keccak_f
        (extract_lane v_N lc ks.Libcrux_sha3.Generic_keccak.f_st l))
  = lemma_keccakf1600_is_rounds v_N ks;
    lemma_keccak_f_is_rounds (extract_lane v_N lc ks.Libcrux_sha3.Generic_keccak.f_st l);
    lemma_rounds_to_spec v_N lc ks (mk_usize 0) l
