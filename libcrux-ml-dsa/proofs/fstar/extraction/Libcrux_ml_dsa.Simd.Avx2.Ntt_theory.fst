module Libcrux_ml_dsa.Simd.Avx2.Ntt_theory
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Avx2.Vector_type in
  ()

(* ============================================================================
   Hand-written companion: the F* theory formerly inlined in the large
   `src/simd/avx2/ntt.rs` `#[hax_lib::fstar::before(...)]` block (the layer
   0/1/2 chunk theory).  Decls are copied BYTE-EXACT from the green extracted
   Libcrux_ml_dsa.Simd.Avx2.Ntt.fst (lines 37-1479); that block was already
   push/pop balanced (40/40) and sat entirely ahead of the first IMPL fn, so no
   outer `#push-options` had to be reconstructed.

   NOTE: several decls here (chunks_of_re_avx2, is_i32b_poly_avx2,
   forall32_elim_1d, ...) share a NAME with `Avx2NttTheory` exports but are
   DISTINCT decls.  `Libcrux_ml_dsa.Simd.Avx2.Ntt` consumes these via `open`
   (bare names) and Avx2NttTheory's via explicit qualification -- exactly as it
   did when this theory was inline.  Do not "unify" them.

   This module is NOT generated -- edit it directly.
   ========================================================================== *)

open Spec.MLDSA.NttConstants

open Spec.Intrinsics

open Core_models
open FStar.Mul
open Spec.MLDSA.Math
module C = Hacspec_ml_dsa.Commute.Chunk
#push-options "--fuel 0 --ifuel 1 --z3rlimit 80"

(* AVX2 analog of Portable's `chunks_of_re`: project the 32 Vec256 SIMD
   units to the flat-chunk view the Commute.Chunk poly lemmas consume.
   Lane access on AVX2 is the bitvec projection `to_i32x8 vec (mk_u64 l)`,
   not the array index `.f_values.[l]` Portable uses. *)
let chunks_of_re_avx2
      (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : t_Array (t_Array i32 (mk_usize 8)) (mk_usize 32)
  = Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 8)) (mk_usize 32)
      #(usize -> t_Array i32 (mk_usize 8))
      (fun (b: usize{b <. mk_usize 32}) ->
         Hacspec_ml_dsa.createi #i32 (mk_usize 8)
           #(usize -> i32)
           (fun (l: usize{l <. mk_usize 8}) ->
              to_i32x8 (Seq.index re (v b)).f_value (mk_u64 (v l))))

(* Index reveal: `chunks_of_re_avx2 re` at chunk b, lane l is the AVX2
   lane projection of unit b.  Two createi_lemma applications. *)
let lemma_chunks_of_re_avx2_index
      (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (b: nat{b < 32}) (l: nat{l < 8})
    : Lemma (Seq.index (Seq.index (chunks_of_re_avx2 re) b) l ==
             to_i32x8 (Seq.index re b).f_value (mk_u64 l))
  = assert (v (mk_usize b) == b);
    assert (v (mk_usize l) == l);
    let inner = Hacspec_ml_dsa.createi #i32 (mk_usize 8)
                  #(usize -> i32)
                  (fun (l: usize{l <. mk_usize 8}) ->
                     to_i32x8 (Seq.index re b).f_value (mk_u64 (v l))) in
    Hacspec_ml_dsa.createi_lemma #(t_Array i32 (mk_usize 8)) (mk_usize 32)
      #(usize -> t_Array i32 (mk_usize 8))
      (fun (b: usize{b <. mk_usize 32}) ->
         Hacspec_ml_dsa.createi #i32 (mk_usize 8)
           #(usize -> i32)
           (fun (l: usize{l <. mk_usize 8}) ->
              to_i32x8 (Seq.index re (v b)).f_value (mk_u64 (v l))))
      (mk_usize b);
    Hacspec_ml_dsa.createi_lemma #i32 (mk_usize 8)
      #(usize -> i32)
      (fun (l: usize{l <. mk_usize 8}) ->
         to_i32x8 (Seq.index re b).f_value (mk_u64 (v l)))
      (mk_usize l)

(* Sanity: the flat view of chunks_of_re_avx2 re, at flat index 8b+l, is
   the AVX2 lane projection — this is what the drivers will rely on to
   bridge AVX2 per-lane posts to the Commute.Chunk simd_units_to_array view. *)
let lemma_flat_avx2_index
      (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (b: nat{b < 32}) (l: nat{l < 8})
    : Lemma (v (Seq.index (C.simd_units_to_array (chunks_of_re_avx2 re)) (8*b + l)) ==
             v (to_i32x8 (Seq.index re b).f_value (mk_u64 l)))
  = C.lemma_simd_units_to_array_reveal (chunks_of_re_avx2 re) b l;
    lemma_chunks_of_re_avx2_index re b l

(* Direct AVX2 per-lane bound predicate.  OPAQUE (mirrors Portable's
   is_i32b_array_opaque / is_i32b_polynomial discipline) so the driver WP never
   expands the 256 per-lane facts; reveal only inside the leaf lemmas. *)
[@@ "opaque_to_smt"]
let is_i32b_poly_avx2 (bnd:nat)
      (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32)) : Type0 =
  forall (u:nat) (l:nat). u < 32 /\ l < 8 ==>
    Spec.Utils.is_i32b bnd (to_i32x8 (Seq.index re u).f_value (mk_u64 l))

(* intro/elim for the opaque bound predicate — consumers cite these, never reveal. *)
let lemma_is_i32b_poly_avx2_elim (bnd:nat)
      (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (u:nat{u<32}) (l:nat{l<8})
    : Lemma (requires is_i32b_poly_avx2 bnd re)
            (ensures Spec.Utils.is_i32b bnd (to_i32x8 (Seq.index re u).f_value (mk_u64 l)))
  = reveal_opaque (`%is_i32b_poly_avx2) is_i32b_poly_avx2

let lemma_is_i32b_poly_avx2_intro (bnd:nat)
      (re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Lemma (requires forall (u:nat) (l:nat). u<32 /\ l<8 ==>
               Spec.Utils.is_i32b bnd (to_i32x8 (Seq.index re u).f_value (mk_u64 l)))
            (ensures is_i32b_poly_avx2 bnd re)
  = reveal_opaque (`%is_i32b_poly_avx2) is_i32b_poly_avx2

(* CRUX (the genuinely-new AVX2 logic): from the per-(b,p) `ntt_step` post +
   zeta bound + input bound, derive the 4 butterfly relations that
   `lemma_ntt_layer_0_step_to_hacspec_poly` consumes.  Input bound only needed
   for add/sub no-overflow exactness (`bnd + FIELD_MAX < pow2 31`); the mont
   mod-q + FIELD_MAX bound hold for ANY input (zeta is bounded by 4190208). *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"
let lemma_l0_pair_relations
      (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (bnd:nat{bnd + 8380416 < pow2 31})
      (b: nat{b < 32}) (p: nat{p < 4})
    : Lemma
        (requires
          is_i32b_poly_avx2 bnd re /\
          (let ci = chunks_of_re_avx2 re in
           let co = chunks_of_re_avx2 re_fut in
           (Seq.index (Seq.index co b) (2*p), Seq.index (Seq.index co b) (2*p+1)) ==
             ntt_step (mk_int (zeta_r (128 + 4*b + p)))
               (Seq.index (Seq.index ci b) (2*p), Seq.index (Seq.index ci b) (2*p+1))))
        (ensures
          (let ci = chunks_of_re_avx2 re in
           let co = chunks_of_re_avx2 re_fut in
           let z : i32 = Hacspec_ml_dsa.Ntt.v_ZETAS.[ mk_usize (4*b + p + 128) ] in
           let zm : i32 = mk_int (zeta_r (128 + 4*b + p)) in
           let t : i32 = mont_mul (Seq.index (Seq.index ci b) (2*p+1)) zm in
           v (Seq.index (Seq.index co b) (2*p))   == v (Seq.index (Seq.index ci b) (2*p)) + v t /\
           v (Seq.index (Seq.index co b) (2*p+1)) == v (Seq.index (Seq.index ci b) (2*p)) - v t /\
           (v t) % 8380417 ==
             (v (Seq.index (Seq.index ci b) (2*p+1)) * v zm * 8265825) % 8380417 /\
           (v zm) % 8380417 == (v z * pow2 32) % 8380417 /\
           // output bound (drives the per-layer bound accumulation chain)
           Spec.Utils.is_i32b (bnd + 8380416) (Seq.index (Seq.index co b) (2*p)) /\
           Spec.Utils.is_i32b (bnd + 8380416) (Seq.index (Seq.index co b) (2*p+1))))
  = let ci = chunks_of_re_avx2 re in
    let co = chunks_of_re_avx2 re_fut in
    let ci_lo = Seq.index (Seq.index ci b) (2*p) in
    let ci_hi = Seq.index (Seq.index ci b) (2*p+1) in
    let co_lo = Seq.index (Seq.index co b) (2*p) in
    let co_hi = Seq.index (Seq.index co b) (2*p+1) in
    let zm : i32 = mk_int (zeta_r (128 + 4*b + p)) in
    let t : i32 = mont_mul ci_hi zm in
    // ntt_step unfolds (non-opaque):
    assert (co_lo == add_mod_opaque ci_lo t);
    assert (co_hi == sub_mod_opaque ci_lo t);
    // input bound on ci_lo (via the opaque-predicate elim, not a raw reveal)
    lemma_chunks_of_re_avx2_index re b (2*p);
    lemma_is_i32b_poly_avx2_elim bnd re b (2*p);
    assert (Spec.Utils.is_i32b bnd ci_lo);
    // mont bound + mod-q (zeta_r bounded by 4190208 < FIELD_MAX)
    assert (Spec.Utils.is_i32b 8380416 zm);
    C.lemma_mont_mul_bound_and_mod_q ci_hi zm;
    assert (Spec.Utils.is_i32b 8380416 t);
    // add/sub exactness (no overflow)
    Spec.Intrinsics.reveal_opaque_arithmetic_ops #i32_inttype;
    assert (v co_lo == v ci_lo + v t);
    assert (v co_hi == v ci_lo - v t);
    // zeta canonicalization
    let idx : nat = 128 + 4*b + p in
    C.lemma_v_zetas_eq_zeta idx
#pop-options

(* ===== Dispatch probe: extract per-(b,p) chunk ntt_step fact from the
   verbatim L0 post (norm[..](forall16(forall4 ..))).  Tests even-parity,
   odd-parity, and a non-zero pair, to confirm the 32x4 dispatch leaf shape
   before generating the full driver. ===== *)
unfold let l0_post (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32)) : Type0 =
  norm [
      primops; iota;
      delta_namespace [`%zeta_r; `%Spec.Utils.forall4; `%Spec.Utils.forall16]
    ]
    (Spec.Utils.forall16 (fun i ->
          let nre = re_fut in
          let re0 = Seq.index re (i * 2) in
          let re1 = Seq.index re (i * 2 + 1) in
          let nre0 = Seq.index nre (i * 2) in
          let nre1 = Seq.index nre (i * 2 + 1) in
          Spec.Utils.forall4 (fun j ->
                let zeta0 = zeta_r (128 + i * 8 + j) in
                let zeta1 = zeta_r (128 + i * 8 + j + 4) in
                let j0 = j * 2 in
                let j1 = j0 + 1 in
                (to_i32x8 nre0.f_value (mk_u64 j0), to_i32x8 nre0.f_value (mk_u64 j1)) ==
                ntt_step (mk_int zeta0)
                  (to_i32x8 re0.f_value (mk_u64 j0), to_i32x8 re0.f_value (mk_u64 j1)) /\
                (to_i32x8 nre1.f_value (mk_u64 j0), to_i32x8 nre1.f_value (mk_u64 j1)) ==
                ntt_step (mk_int zeta1)
                  (to_i32x8 re1.f_value (mk_u64 j0), to_i32x8 re1.f_value (mk_u64 j1)))))

unfold let chunkfact (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
                     (b:nat{b<32}) (p:nat{p<4}) : Type0 =
  let ci = chunks_of_re_avx2 re in
  let co = chunks_of_re_avx2 re_fut in
  (Seq.index (Seq.index co b) (2*p), Seq.index (Seq.index co b) (2*p+1)) ==
    ntt_step (mk_int (zeta_r (128 + 4*b + p)))
      (Seq.index (Seq.index ci b) (2*p), Seq.index (Seq.index ci b) (2*p+1))


(* ===== ARCHITECTURE TEST: cheap 16-arm forall16-elim against the SYMBOLIC
   post (zeta_r NOT norm-evaluated).  Each arm is a direct-conjunct match
   (forall32_elim_1d style) — should be fast, unlike the 128-leaf search. ===== *)
unfold let l0_post_sym (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32)) : Type0 =
  norm [
      primops; iota;
      delta_namespace [`%Spec.Utils.forall4; `%Spec.Utils.forall16]
    ]
    (Spec.Utils.forall16 (fun i ->
          let nre = re_fut in
          let re0 = Seq.index re (i * 2) in
          let re1 = Seq.index re (i * 2 + 1) in
          let nre0 = Seq.index nre (i * 2) in
          let nre1 = Seq.index nre (i * 2 + 1) in
          Spec.Utils.forall4 (fun j ->
                let zeta0 = zeta_r (128 + i * 8 + j) in
                let zeta1 = zeta_r (128 + i * 8 + j + 4) in
                let j0 = j * 2 in
                let j1 = j0 + 1 in
                (to_i32x8 nre0.f_value (mk_u64 j0), to_i32x8 nre0.f_value (mk_u64 j1)) ==
                ntt_step (mk_int zeta0)
                  (to_i32x8 re0.f_value (mk_u64 j0), to_i32x8 re0.f_value (mk_u64 j1)) /\
                (to_i32x8 nre1.f_value (mk_u64 j0), to_i32x8 nre1.f_value (mk_u64 j1)) ==
                ntt_step (mk_int zeta1)
                  (to_i32x8 re1.f_value (mk_u64 j0), to_i32x8 re1.f_value (mk_u64 j1)))))

unfold let l0_body (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
                   (i:nat{i<16}) : Type0 =
  let re0 = Seq.index re (i*2) in
  let re1 = Seq.index re (i*2+1) in
  let nre0 = Seq.index re_fut (i*2) in
  let nre1 = Seq.index re_fut (i*2+1) in
  Spec.Utils.forall4 (fun j ->
        let zeta0 = zeta_r (128 + i*8 + j) in
        let zeta1 = zeta_r (128 + i*8 + j + 4) in
        let j0 = j*2 in let j1 = j0+1 in
        (to_i32x8 nre0.f_value (mk_u64 j0), to_i32x8 nre0.f_value (mk_u64 j1)) ==
          ntt_step (mk_int zeta0) (to_i32x8 re0.f_value (mk_u64 j0), to_i32x8 re0.f_value (mk_u64 j1)) /\
        (to_i32x8 nre1.f_value (mk_u64 j0), to_i32x8 nre1.f_value (mk_u64 j1)) ==
          ntt_step (mk_int zeta1) (to_i32x8 re1.f_value (mk_u64 j0), to_i32x8 re1.f_value (mk_u64 j1)))

(* Generic forall16-elim with ABSTRACT r (mirrors Portable forall32_elim_1d):
   each arm is a cheap direct-conjunct match because `r i` is opaque — no heavy
   body reduction.  The expensive l0_body is only substituted at the call. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 40"
let forall16_elim_1d (r: (i: nat{i < 16}) -> Type0)
    : Lemma (requires Spec.Utils.forall16 r) (ensures forall (i: nat{i < 16}). r i)
  = let aux (i: nat{i < 16}) : Lemma (r i) =
      (match i with
       | 0 -> () | 1 -> () | 2 -> () | 3 -> () | 4 -> () | 5 -> () | 6 -> () | 7 -> ()
       | 8 -> () | 9 -> () | 10 -> () | 11 -> () | 12 -> () | 13 -> () | 14 -> () | _ -> ())
    in Classical.forall_intro aux
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 60"
let lemma_lift (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Lemma (requires l0_post_sym re re_fut)
            (ensures forall (i:nat{i<16}). l0_body re re_fut i)
  = forall16_elim_1d (l0_body re re_fut)
#pop-options

(* ===== Final L0 glue: forall i. l0_body i  ==>  forall (b,p). chunkfact b p.
   Per-(b,p): instantiate i=b/2 (Euclidean), parity split (nre0/nre1), index lemmas. ===== *)
unfold let body2 (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
                 (i:nat{i<16}) (j:nat{j<4}) : Type0 =
  let re0 = Seq.index re (i*2) in
  let re1 = Seq.index re (i*2+1) in
  let nre0 = Seq.index re_fut (i*2) in
  let nre1 = Seq.index re_fut (i*2+1) in
  let zeta0 = zeta_r (128 + i*8 + j) in
  let zeta1 = zeta_r (128 + i*8 + j + 4) in
  let j0 = j*2 in let j1 = j0+1 in
  (to_i32x8 nre0.f_value (mk_u64 j0), to_i32x8 nre0.f_value (mk_u64 j1)) ==
    ntt_step (mk_int zeta0) (to_i32x8 re0.f_value (mk_u64 j0), to_i32x8 re0.f_value (mk_u64 j1)) /\
  (to_i32x8 nre1.f_value (mk_u64 j0), to_i32x8 nre1.f_value (mk_u64 j1)) ==
    ntt_step (mk_int zeta1) (to_i32x8 re1.f_value (mk_u64 j0), to_i32x8 re1.f_value (mk_u64 j1))

#push-options "--fuel 0 --ifuel 1 --z3rlimit 40"
let forall4_elim_1d (r: (j: nat{j < 4}) -> Type0)
    : Lemma (requires Spec.Utils.forall4 r) (ensures forall (j: nat{j < 4}). r j)
  = let aux (j: nat{j < 4}) : Lemma (r j) =
      (match j with | 0 -> () | 1 -> () | 2 -> () | _ -> ())
    in Classical.forall_intro aux
#pop-options

(* l0_body i is definitionally forall4 (fun j -> body2 i j); lift to forall i j. body2. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 80"
let lemma_lift2 (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Lemma (requires l0_post_sym re re_fut)
            (ensures forall (i:nat{i<16}) (j:nat{j<4}). body2 re re_fut i j)
  = lemma_lift re re_fut;
    let aux (i:nat{i<16}) : Lemma (forall (j:nat{j<4}). body2 re re_fut i j) =
      forall4_elim_1d (fun (j:nat{j<4}) -> body2 re re_fut i j)
    in Classical.forall_intro aux
#pop-options

(* ===== From the symbolic L0 post (16x4 ntt_step facts) to the 32x4 chunk
   ntt_step facts the bridge consumes.  Per (b,p): instantiate i=b/2, parity of b
   selects nre0/nre1, index lemmas bridge to_i32x8 <-> chunks_of_re_avx2. ===== *)
(* Even chunk b=2i: chunkfact (2i) p comes from body2 i p's nre0 part. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"
let lemma_chunkfact_even
      (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (i:nat{i<16}) (p:nat{p<4})
    : Lemma (requires body2 re re_fut i p) (ensures chunkfact re re_fut (2*i) p)
  = lemma_chunks_of_re_avx2_index re (2*i) (2*p);
    lemma_chunks_of_re_avx2_index re (2*i) (2*p+1);
    lemma_chunks_of_re_avx2_index re_fut (2*i) (2*p);
    lemma_chunks_of_re_avx2_index re_fut (2*i) (2*p+1)
#pop-options

(* Odd chunk b=2i+1: chunkfact (2i+1) p comes from body2 i p's nre1 part. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"
let lemma_chunkfact_odd
      (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (i:nat{i<16}) (p:nat{p<4})
    : Lemma (requires body2 re re_fut i p) (ensures chunkfact re re_fut (2*i+1) p)
  = lemma_chunks_of_re_avx2_index re (2*i+1) (2*p);
    lemma_chunks_of_re_avx2_index re (2*i+1) (2*p+1);
    lemma_chunks_of_re_avx2_index re_fut (2*i+1) (2*p);
    lemma_chunks_of_re_avx2_index re_fut (2*i+1) (2*p+1)
#pop-options

(* Generic createi-free re-index: even/odd 16-foralls -> 32-forall.  ABSTRACT q
   so no chunkfact/createi term enters this VC (kills the asymmetric odd-branch
   cascade). *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"
let reindex_32_from_16 (q: (b:nat{b<32}) -> (p:nat{p<4}) -> Type0)
    : Lemma (requires (forall (i:nat{i<16}) (p:nat{p<4}). q (2*i) p) /\
                      (forall (i:nat{i<16}) (p:nat{p<4}). q (2*i+1) p))
            (ensures forall (b:nat{b<32}) (p:nat{p<4}). q b p)
  = let aux (b:nat{b<32}) (p:nat{p<4}) : Lemma (q b p) =
      FStar.Math.Lemmas.euclidean_division_definition b 2;
      (if b % 2 = 0 then assert (q (2*(b/2)) p) else assert (q (2*(b/2)+1) p))
    in Classical.forall_intro_2 aux
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"
let lemma_chunkfacts_from_lift
      (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Lemma (requires l0_post_sym re re_fut)
            (ensures forall (b:nat{b<32}) (p:nat{p<4}). chunkfact re re_fut b p)
  = lemma_lift2 re re_fut;
    (* even chunks 2i: instantiate body2 at CLEAN i (no b/2 mess) *)
    let auxe (i:nat{i<16}) (p:nat{p<4}) : Lemma (chunkfact re re_fut (2*i) p) =
      lemma_chunkfact_even re re_fut i p
    in Classical.forall_intro_2 auxe;
    (* odd chunks 2i+1 *)
    let auxo (i:nat{i<16}) (p:nat{p<4}) : Lemma (chunkfact re re_fut (2*i+1) p) =
      lemma_chunkfact_odd re re_fut i p
    in Classical.forall_intro_2 auxo;
    reindex_32_from_16 (chunkfact re re_fut)
#pop-options

(* ===== L0 opaque per-chunk FE atom (AVX2 form: t_p = mont_mul (ci[2p+1]) z_p).
   Mirror of Portable's unit_fe_post_l0; opaque so the driver composes 32 of
   them like the bounds post, never expanding 256 facts into the WP. ===== *)
[@@ "opaque_to_smt"]
let unit_post_l0_avx2 (ci co: t_Array i32 (mk_usize 8))
      (zeta0 zeta1 zeta2 zeta3: i32{Spec.Utils.is_i32b 4190208 zeta0 /\ Spec.Utils.is_i32b 4190208 zeta1 /\ Spec.Utils.is_i32b 4190208 zeta2 /\ Spec.Utils.is_i32b 4190208 zeta3}) : Type0 =
  (let t0 = mont_mul (Seq.index ci 1) zeta0 in
   let t1 = mont_mul (Seq.index ci 3) zeta1 in
   let t2 = mont_mul (Seq.index ci 5) zeta2 in
   let t3 = mont_mul (Seq.index ci 7) zeta3 in
   v (Seq.index co 0) == v (Seq.index ci 0) + v t0 /\
   v (Seq.index co 1) == v (Seq.index ci 0) - v t0 /\
   (v t0) % 8380417 == (v (Seq.index ci 1) * v zeta0 * 8265825) % 8380417 /\
   v (Seq.index co 2) == v (Seq.index ci 2) + v t1 /\
   v (Seq.index co 3) == v (Seq.index ci 2) - v t1 /\
   (v t1) % 8380417 == (v (Seq.index ci 3) * v zeta1 * 8265825) % 8380417 /\
   v (Seq.index co 4) == v (Seq.index ci 4) + v t2 /\
   v (Seq.index co 5) == v (Seq.index ci 4) - v t2 /\
   (v t2) % 8380417 == (v (Seq.index ci 5) * v zeta2 * 8265825) % 8380417 /\
   v (Seq.index co 6) == v (Seq.index ci 6) + v t3 /\
   v (Seq.index co 7) == v (Seq.index ci 6) - v t3 /\
   (v t3) % 8380417 == (v (Seq.index ci 7) * v zeta3 * 8265825) % 8380417)

(* Standalone: unfold one L0 opaque atom to the bridge's per-pair forall. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 100 --split_queries always --z3refresh"
let lemma_atom_to_bf_l0_avx2 (ci co: t_Array i32 (mk_usize 8))
      (zf: (p: nat{p < 4}) -> (z: i32{Spec.Utils.is_i32b 4190208 z}))
    : Lemma (requires unit_post_l0_avx2 ci co (zf 0) (zf 1) (zf 2) (zf 3))
            (ensures
              (forall (p: nat{p < 4}).
                (let t = mont_mul (Seq.index ci (2*p+1)) (zf p) in
                 v (Seq.index co (2*p))   == v (Seq.index ci (2*p)) + v t /\
                 v (Seq.index co (2*p+1)) == v (Seq.index ci (2*p)) - v t /\
                 (v t) % 8380417 == (v (Seq.index ci (2*p+1)) * v (zf p) * 8265825) % 8380417)))
  = reveal_opaque (`%unit_post_l0_avx2) unit_post_l0_avx2;
    introduce forall (p: nat{p < 4}).
        (let t = mont_mul (Seq.index ci (2*p+1)) (zf p) in
         v (Seq.index co (2*p))   == v (Seq.index ci (2*p)) + v t /\
         v (Seq.index co (2*p+1)) == v (Seq.index ci (2*p)) - v t /\
         (v t) % 8380417 == (v (Seq.index ci (2*p+1)) * v (zf p) * 8265825) % 8380417)
    with (match p with | 0 -> () | 1 -> () | 2 -> () | _ -> ())
#pop-options

(* ===== Per-chunk establishment: from the input bound + the 4 chunk ntt_step
   facts, build the opaque atom for chunk b AND the per-lane output bound.
   The genuinely-new AVX2 logic lives in lemma_l0_pair_relations (already
   validated); this just packages 4 pairs into the atom + bound. ===== *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 200 --split_queries always --z3refresh"
let lemma_l0_chunk_avx2
      (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (bnd:nat{bnd + 8380416 < pow2 31})
      (b: nat{b < 32})
    : Lemma
        (requires is_i32b_poly_avx2 bnd re /\ (forall (p:nat{p<4}). chunkfact re re_fut b p))
        (ensures
          unit_post_l0_avx2 (Seq.index (chunks_of_re_avx2 re) b) (Seq.index (chunks_of_re_avx2 re_fut) b)
            (mk_i32 (zeta_r (4*b + 0 + 128))) (mk_i32 (zeta_r (4*b + 1 + 128)))
            (mk_i32 (zeta_r (4*b + 2 + 128))) (mk_i32 (zeta_r (4*b + 3 + 128))) /\
          (forall (l:nat). l < 8 ==>
            Spec.Utils.is_i32b (bnd + 8380416) (to_i32x8 (Seq.index re_fut b).f_value (mk_u64 l))))
  = lemma_l0_pair_relations re re_fut bnd b 0;
    lemma_l0_pair_relations re re_fut bnd b 1;
    lemma_l0_pair_relations re re_fut bnd b 2;
    lemma_l0_pair_relations re re_fut bnd b 3;
    reveal_opaque (`%unit_post_l0_avx2) unit_post_l0_avx2;
    introduce forall (l:nat{l<8}).
        Spec.Utils.is_i32b (bnd + 8380416) (to_i32x8 (Seq.index re_fut b).f_value (mk_u64 l))
    with (lemma_chunks_of_re_avx2_index re_fut b l)
#pop-options

(* Generic 1D ground->symbolic forall lift for 32 (mirror of forall16_elim_1d). *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 40"
let forall32_elim_1d (r: (b: nat{b < 32}) -> Type0)
    : Lemma (requires Spec.Utils.forall32 r) (ensures forall (b: nat{b < 32}). r b)
  = let aux (b: nat{b < 32}) : Lemma (r b) =
      (match b with
       | 0 -> () | 1 -> () | 2 -> () | 3 -> () | 4 -> () | 5 -> () | 6 -> () | 7 -> ()
       | 8 -> () | 9 -> () | 10 -> () | 11 -> () | 12 -> () | 13 -> () | 14 -> () | 15 -> ()
       | 16 -> () | 17 -> () | 18 -> () | 19 -> () | 20 -> () | 21 -> () | 22 -> () | 23 -> ()
       | 24 -> () | 25 -> () | 26 -> () | 27 -> () | 28 -> () | 29 -> () | 30 -> () | _ -> ())
    in Classical.forall_intro aux
#pop-options

(* ===== Clean-context driver composition for L0 (chunk arrays): from the
   forall32 of opaque atoms, feed the Commute.Chunk poly lemma.  Mirror of
   Portable lemma_l0_driver_compose with mont_mul + the AVX2 atom. ===== *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 200 --split_queries always --z3refresh"
let lemma_l0_driver_compose_avx2
      (orig fut: t_Array (t_Array i32 (mk_usize 8)) (mk_usize 32))
    : Lemma
        (requires
          forall32 (fun b ->
            unit_post_l0_avx2 (Seq.index orig b) (Seq.index fut b)
              (mk_i32 (zeta_r (4*b + 0 + 128))) (mk_i32 (zeta_r (4*b + 1 + 128)))
              (mk_i32 (zeta_r (4*b + 2 + 128))) (mk_i32 (zeta_r (4*b + 3 + 128)))))
        (ensures
          (let in_flat = C.simd_units_to_array orig in
           let out_flat = C.simd_units_to_array fut in
           let spec = Hacspec_ml_dsa.Ntt.ntt_layer in_flat (mk_usize 0) in
           forall (i: nat). i < 256 ==>
             (v (Seq.index out_flat i)) % 8380417 == (v (Seq.index spec i)) % 8380417))
  = let zm (b: nat{b < 32}) (p: nat{p < 4}) : (z: i32{Spec.Utils.is_i32b 4190208 z}) =
      mk_i32 (zeta_r (4*b + p + 128)) in
    let t (b: nat{b < 32}) (p: nat{p < 4}) : i32 =
      mont_mul (Seq.index (Seq.index orig b) (2*p+1)) (zm b p) in
    forall32_elim_1d (fun b -> unit_post_l0_avx2 (Seq.index orig b) (Seq.index fut b)
                                 (mk_i32 (zeta_r (4*b + 0 + 128))) (mk_i32 (zeta_r (4*b + 1 + 128)))
                                 (mk_i32 (zeta_r (4*b + 2 + 128))) (mk_i32 (zeta_r (4*b + 3 + 128))));
    (let aux (b: nat{b < 32}) (p: nat{p < 4}) : Lemma
       (let ci = Seq.index orig b in
        let co = Seq.index fut b in
        v (Seq.index co (2*p))   == v (Seq.index ci (2*p)) + v (t b p) /\
        v (Seq.index co (2*p+1)) == v (Seq.index ci (2*p)) - v (t b p) /\
        (v (t b p)) % 8380417 == (v (Seq.index ci (2*p+1)) * v (zm b p) * 8265825) % 8380417 /\
        (v (zm b p)) % 8380417 ==
          (v (Hacspec_ml_dsa.Ntt.v_ZETAS.[ mk_usize (4*b + p + 128) ] <: i32) * pow2 32) % 8380417)
      = lemma_atom_to_bf_l0_avx2 (Seq.index orig b) (Seq.index fut b) (fun p -> zm b p);
        reveal_opaque (`%Spec.MLDSA.Math.mod_q) (Spec.MLDSA.Math.mod_q);
        let _ = zeta_r (4*b + p + 128) in
        C.lemma_v_zetas_eq_zeta (4*b + p + 128)
     in Classical.forall_intro_2 aux);
    C.lemma_ntt_layer_0_step_to_hacspec_poly orig fut t zm
#pop-options

(* ===== FULL L0 body glue: from input bound + the symbolic L0 post, derive the
   complete layer-fn post (output bound + functional congruence).  This is what
   the ntt.rs body tail calls (after establishing l0_post_sym from the butterfly
   facts via assert_norm zeta literals). ===== *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 200 --split_queries always --z3refresh"
let lemma_l0_full_avx2
      (orig_re re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (bnd:nat{bnd + 8380416 < pow2 31})
    : Lemma
        (requires is_i32b_poly_avx2 bnd orig_re /\ l0_post_sym orig_re re)
        (ensures
          is_i32b_poly_avx2 (bnd + 8380416) re /\
          (let in_flat = C.simd_units_to_array (chunks_of_re_avx2 orig_re) in
           let out_flat = C.simd_units_to_array (chunks_of_re_avx2 re) in
           let spec = Hacspec_ml_dsa.Ntt.ntt_layer in_flat (mk_usize 0) in
           forall (i: nat). i < 256 ==>
             (v (Seq.index out_flat i)) % 8380417 == (v (Seq.index spec i)) % 8380417))
  = lemma_chunkfacts_from_lift orig_re re;
    let aux (b:nat{b<32}) : Lemma
        (unit_post_l0_avx2 (Seq.index (chunks_of_re_avx2 orig_re) b) (Seq.index (chunks_of_re_avx2 re) b)
           (mk_i32 (zeta_r (4*b + 0 + 128))) (mk_i32 (zeta_r (4*b + 1 + 128)))
           (mk_i32 (zeta_r (4*b + 2 + 128))) (mk_i32 (zeta_r (4*b + 3 + 128)))
         /\ (forall (l:nat). l<8 ==>
              Spec.Utils.is_i32b (bnd + 8380416) (to_i32x8 (Seq.index re b).f_value (mk_u64 l))))
      = lemma_l0_chunk_avx2 orig_re re bnd b
    in Classical.forall_intro aux;
    lemma_is_i32b_poly_avx2_intro (bnd + 8380416) re;
    lemma_l0_driver_compose_avx2 (chunks_of_re_avx2 orig_re) (chunks_of_re_avx2 re)
#pop-options

(* ===== Bridge: the body-natural literal-zeta L0 post (l0_post) implies the
   symbolic-zeta form (l0_post_sym) the lift machinery consumes.  128 zeta_r
   literal assert_norms.  This is what the ntt.rs body calls after the
   butterflies establish l0_post. ===== *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"
let lemma_l0post_to_sym (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Lemma (requires l0_post re re_fut) (ensures l0_post_sym re re_fut)
  = 
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 128 == 2091667);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 129 == 3407706);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 130 == 2316500);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 131 == 3817976);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 132 == (- 3342478));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 133 == 2244091);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 134 == (- 2446433));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 135 == (- 3562462));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 136 == 266997);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 137 == 2434439);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 138 == (- 1235728));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 139 == 3513181);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 140 == (- 3520352));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 141 == (- 3759364));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 142 == (- 1197226));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 143 == (- 3193378));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 144 == 900702);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 145 == 1859098);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 146 == 909542);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 147 == 819034);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 148 == 495491);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 149 == (- 1613174));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 150 == (- 43260));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 151 == (- 522500));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 152 == (- 655327));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 153 == (- 3122442));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 154 == 2031748);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 155 == 3207046);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 156 == (- 3556995));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 157 == (- 525098));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 158 == (- 768622));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 159 == (- 3595838));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 160 == 342297);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 161 == 286988);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 162 == (- 2437823));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 163 == 4108315);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 164 == 3437287);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 165 == (- 3342277));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 166 == 1735879);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 167 == 203044);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 168 == 2842341);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 169 == 2691481);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 170 == (- 2590150));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 171 == 1265009);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 172 == 4055324);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 173 == 1247620);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 174 == 2486353);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 175 == 1595974);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 176 == (- 3767016));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 177 == 1250494);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 178 == 2635921);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 179 == (- 3548272));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 180 == (- 2994039));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 181 == 1869119);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 182 == 1903435);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 183 == (- 1050970));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 184 == (- 1333058));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 185 == 1237275);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 186 == (- 3318210));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 187 == (- 1430225));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 188 == (- 451100));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 189 == 1312455);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 190 == 3306115);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 191 == (- 1962642));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 192 == (- 1279661));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 193 == 1917081);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 194 == (- 2546312));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 195 == (- 1374803));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 196 == 1500165);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 197 == 777191);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 198 == 2235880);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 199 == 3406031);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 200 == (- 542412));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 201 == (- 2831860));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 202 == (- 1671176));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 203 == (- 1846953));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 204 == (- 2584293));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 205 == (- 3724270));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 206 == 594136);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 207 == (- 3776993));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 208 == (- 2013608));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 209 == 2432395);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 210 == 2454455);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 211 == (- 164721));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 212 == 1957272);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 213 == 3369112);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 214 == 185531);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 215 == (- 1207385));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 216 == (- 3183426));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 217 == 162844);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 218 == 1616392);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 219 == 3014001);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 220 == 810149);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 221 == 1652634);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 222 == (- 3694233));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 223 == (- 1799107));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 224 == (- 3038916));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 225 == 3523897);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 226 == 3866901);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 227 == 269760);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 228 == 2213111);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 229 == (- 975884));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 230 == 1717735);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 231 == 472078);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 232 == (- 426683));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 233 == 1723600);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 234 == (- 1803090));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 235 == 1910376);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 236 == (- 1667432));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 237 == (- 1104333));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 238 == (- 260646));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 239 == (- 3833893));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 240 == (- 2939036));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 241 == (- 2235985));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 242 == (- 420899));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 243 == (- 2286327));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 244 == 183443);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 245 == (- 976891));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 246 == 1612842);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 247 == (- 3545687));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 248 == (- 554416));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 249 == 3919660);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 250 == (- 48306));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 251 == (- 1362209));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 252 == 3937738);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 253 == 1400424);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 254 == (- 846154));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 255 == 1976782)
#pop-options
(* CRUX: from the per-(b,p) ntt_step post (pair (p,p+4), zeta = zeta_r(b+32))
   + zeta bound + input bound, derive the butterfly relations + output bound. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"
let lemma_l2_pair_relations
      (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (bnd:nat{bnd + 8380416 < pow2 31})
      (b: nat{b < 32}) (p: nat{p < 4})
    : Lemma
        (requires
          is_i32b_poly_avx2 bnd re /\
          (let ci = chunks_of_re_avx2 re in
           let co = chunks_of_re_avx2 re_fut in
           (Seq.index (Seq.index co b) p, Seq.index (Seq.index co b) (p+4)) ==
             ntt_step (mk_int (zeta_r (b + 32)))
               (Seq.index (Seq.index ci b) p, Seq.index (Seq.index ci b) (p+4))))
        (ensures
          (let ci = chunks_of_re_avx2 re in
           let co = chunks_of_re_avx2 re_fut in
           let z : i32 = Hacspec_ml_dsa.Ntt.v_ZETAS.[ mk_usize (b + 32) ] in
           let zm : i32 = mk_int (zeta_r (b + 32)) in
           let t : i32 = mont_mul (Seq.index (Seq.index ci b) (p+4)) zm in
           v (Seq.index (Seq.index co b) p)     == v (Seq.index (Seq.index ci b) p) + v t /\
           v (Seq.index (Seq.index co b) (p+4)) == v (Seq.index (Seq.index ci b) p) - v t /\
           (v t) % 8380417 ==
             (v (Seq.index (Seq.index ci b) (p+4)) * v zm * 8265825) % 8380417 /\
           (v zm) % 8380417 == (v z * pow2 32) % 8380417 /\
           Spec.Utils.is_i32b (bnd + 8380416) (Seq.index (Seq.index co b) p) /\
           Spec.Utils.is_i32b (bnd + 8380416) (Seq.index (Seq.index co b) (p+4))))
  = let ci = chunks_of_re_avx2 re in
    let co = chunks_of_re_avx2 re_fut in
    let ci_lo = Seq.index (Seq.index ci b) p in
    let ci_hi = Seq.index (Seq.index ci b) (p+4) in
    let co_lo = Seq.index (Seq.index co b) p in
    let co_hi = Seq.index (Seq.index co b) (p+4) in
    let zm : i32 = mk_int (zeta_r (b + 32)) in
    let t : i32 = mont_mul ci_hi zm in
    assert (co_lo == add_mod_opaque ci_lo t);
    assert (co_hi == sub_mod_opaque ci_lo t);
    lemma_chunks_of_re_avx2_index re b p;
    lemma_is_i32b_poly_avx2_elim bnd re b p;
    assert (Spec.Utils.is_i32b bnd ci_lo);
    assert (Spec.Utils.is_i32b 8380416 zm);
    C.lemma_mont_mul_bound_and_mod_q ci_hi zm;
    assert (Spec.Utils.is_i32b 8380416 t);
    Spec.Intrinsics.reveal_opaque_arithmetic_ops #i32_inttype;
    assert (v co_lo == v ci_lo + v t);
    assert (v co_hi == v ci_lo - v t);
    let idx : nat = b + 32 in
    C.lemma_v_zetas_eq_zeta idx
#pop-options

(* Verbatim literal-zeta L2 post (matches ntt_at_layer_2_'s ensures). *)
unfold let l2_post (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32)) : Type0 =
  norm [
      primops; iota;
      delta_namespace [`%zeta_r; `%Spec.Utils.forall4; `%Spec.Utils.forall16]
    ]
    (Spec.Utils.forall16 (fun i ->
          let nre = re_fut in
          let re0 = Seq.index re (i * 2) in
          let re1 = Seq.index re (i * 2 + 1) in
          let nre0 = Seq.index nre (i * 2) in
          let nre1 = Seq.index nre (i * 2 + 1) in
          Spec.Utils.forall4 (fun j ->
                let zeta0 = zeta_r (32 + i * 2) in
                let zeta1 = zeta_r (32 + i * 2 + 1) in
                let j0 = j in
                let j1 = j0 + 4 in
                (to_i32x8 nre0.f_value (mk_u64 j0), to_i32x8 nre0.f_value (mk_u64 j1)) ==
                ntt_step (mk_int zeta0)
                  (to_i32x8 re0.f_value (mk_u64 j0), to_i32x8 re0.f_value (mk_u64 j1)) /\
                (to_i32x8 nre1.f_value (mk_u64 j0), to_i32x8 nre1.f_value (mk_u64 j1)) ==
                ntt_step (mk_int zeta1)
                  (to_i32x8 re1.f_value (mk_u64 j0), to_i32x8 re1.f_value (mk_u64 j1)))))

unfold let chunkfact_l2 (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
                        (b:nat{b<32}) (p:nat{p<4}) : Type0 =
  let ci = chunks_of_re_avx2 re in
  let co = chunks_of_re_avx2 re_fut in
  (Seq.index (Seq.index co b) p, Seq.index (Seq.index co b) (p+4)) ==
    ntt_step (mk_int (zeta_r (b + 32)))
      (Seq.index (Seq.index ci b) p, Seq.index (Seq.index ci b) (p+4))

(* Symbolic-zeta L2 post (zeta_r NOT norm-evaluated). *)
unfold let l2_post_sym (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32)) : Type0 =
  norm [
      primops; iota;
      delta_namespace [`%Spec.Utils.forall4; `%Spec.Utils.forall16]
    ]
    (Spec.Utils.forall16 (fun i ->
          let nre = re_fut in
          let re0 = Seq.index re (i * 2) in
          let re1 = Seq.index re (i * 2 + 1) in
          let nre0 = Seq.index nre (i * 2) in
          let nre1 = Seq.index nre (i * 2 + 1) in
          Spec.Utils.forall4 (fun j ->
                let zeta0 = zeta_r (32 + i * 2) in
                let zeta1 = zeta_r (32 + i * 2 + 1) in
                let j0 = j in
                let j1 = j0 + 4 in
                (to_i32x8 nre0.f_value (mk_u64 j0), to_i32x8 nre0.f_value (mk_u64 j1)) ==
                ntt_step (mk_int zeta0)
                  (to_i32x8 re0.f_value (mk_u64 j0), to_i32x8 re0.f_value (mk_u64 j1)) /\
                (to_i32x8 nre1.f_value (mk_u64 j0), to_i32x8 nre1.f_value (mk_u64 j1)) ==
                ntt_step (mk_int zeta1)
                  (to_i32x8 re1.f_value (mk_u64 j0), to_i32x8 re1.f_value (mk_u64 j1)))))

unfold let l2_body (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
                   (i:nat{i<16}) : Type0 =
  let re0 = Seq.index re (i*2) in
  let re1 = Seq.index re (i*2+1) in
  let nre0 = Seq.index re_fut (i*2) in
  let nre1 = Seq.index re_fut (i*2+1) in
  Spec.Utils.forall4 (fun j ->
        let zeta0 = zeta_r (32 + i*2) in
        let zeta1 = zeta_r (32 + i*2 + 1) in
        let j0 = j in let j1 = j0+4 in
        (to_i32x8 nre0.f_value (mk_u64 j0), to_i32x8 nre0.f_value (mk_u64 j1)) ==
          ntt_step (mk_int zeta0) (to_i32x8 re0.f_value (mk_u64 j0), to_i32x8 re0.f_value (mk_u64 j1)) /\
        (to_i32x8 nre1.f_value (mk_u64 j0), to_i32x8 nre1.f_value (mk_u64 j1)) ==
          ntt_step (mk_int zeta1) (to_i32x8 re1.f_value (mk_u64 j0), to_i32x8 re1.f_value (mk_u64 j1)))

#push-options "--fuel 0 --ifuel 1 --z3rlimit 60"
let lemma_lift_l2 (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Lemma (requires l2_post_sym re re_fut)
            (ensures forall (i:nat{i<16}). l2_body re re_fut i)
  = forall16_elim_1d (l2_body re re_fut)
#pop-options

unfold let body2_l2 (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
                    (i:nat{i<16}) (j:nat{j<4}) : Type0 =
  let re0 = Seq.index re (i*2) in
  let re1 = Seq.index re (i*2+1) in
  let nre0 = Seq.index re_fut (i*2) in
  let nre1 = Seq.index re_fut (i*2+1) in
  let zeta0 = zeta_r (32 + i*2) in
  let zeta1 = zeta_r (32 + i*2 + 1) in
  let j0 = j in let j1 = j0+4 in
  (to_i32x8 nre0.f_value (mk_u64 j0), to_i32x8 nre0.f_value (mk_u64 j1)) ==
    ntt_step (mk_int zeta0) (to_i32x8 re0.f_value (mk_u64 j0), to_i32x8 re0.f_value (mk_u64 j1)) /\
  (to_i32x8 nre1.f_value (mk_u64 j0), to_i32x8 nre1.f_value (mk_u64 j1)) ==
    ntt_step (mk_int zeta1) (to_i32x8 re1.f_value (mk_u64 j0), to_i32x8 re1.f_value (mk_u64 j1))

#push-options "--fuel 0 --ifuel 1 --z3rlimit 80"
let lemma_lift2_l2 (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Lemma (requires l2_post_sym re re_fut)
            (ensures forall (i:nat{i<16}) (j:nat{j<4}). body2_l2 re re_fut i j)
  = lemma_lift_l2 re re_fut;
    let aux (i:nat{i<16}) : Lemma (forall (j:nat{j<4}). body2_l2 re re_fut i j) =
      forall4_elim_1d (fun (j:nat{j<4}) -> body2_l2 re re_fut i j)
    in Classical.forall_intro aux
#pop-options

(* Even chunk b=2i: chunkfact_l2 (2i) p from body2_l2 i p's nre0 part. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"
let lemma_chunkfact_l2_even
      (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (i:nat{i<16}) (p:nat{p<4})
    : Lemma (requires body2_l2 re re_fut i p) (ensures chunkfact_l2 re re_fut (2*i) p)
  = lemma_chunks_of_re_avx2_index re (2*i) p;
    lemma_chunks_of_re_avx2_index re (2*i) (p+4);
    lemma_chunks_of_re_avx2_index re_fut (2*i) p;
    lemma_chunks_of_re_avx2_index re_fut (2*i) (p+4)
#pop-options

(* Odd chunk b=2i+1: chunkfact_l2 (2i+1) p from body2_l2 i p's nre1 part. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"
let lemma_chunkfact_l2_odd
      (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (i:nat{i<16}) (p:nat{p<4})
    : Lemma (requires body2_l2 re re_fut i p) (ensures chunkfact_l2 re re_fut (2*i+1) p)
  = lemma_chunks_of_re_avx2_index re (2*i+1) p;
    lemma_chunks_of_re_avx2_index re (2*i+1) (p+4);
    lemma_chunks_of_re_avx2_index re_fut (2*i+1) p;
    lemma_chunks_of_re_avx2_index re_fut (2*i+1) (p+4)
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"
let lemma_chunkfacts_from_lift_l2
      (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Lemma (requires l2_post_sym re re_fut)
            (ensures forall (b:nat{b<32}) (p:nat{p<4}). chunkfact_l2 re re_fut b p)
  = lemma_lift2_l2 re re_fut;
    let auxe (i:nat{i<16}) (p:nat{p<4}) : Lemma (chunkfact_l2 re re_fut (2*i) p) =
      lemma_chunkfact_l2_even re re_fut i p
    in Classical.forall_intro_2 auxe;
    let auxo (i:nat{i<16}) (p:nat{p<4}) : Lemma (chunkfact_l2 re re_fut (2*i+1) p) =
      lemma_chunkfact_l2_odd re re_fut i p
    in Classical.forall_intro_2 auxo;
    reindex_32_from_16 (chunkfact_l2 re re_fut)
#pop-options

(* L2 opaque per-chunk FE atom: ONE zeta, pairs (p,p+4), t_p = mont_mul (ci[p+4]) zeta. *)
[@@ "opaque_to_smt"]
let unit_post_l2_avx2 (ci co: t_Array i32 (mk_usize 8))
      (zeta: i32{Spec.Utils.is_i32b 4190208 zeta}) : Type0 =
  (let t0 = mont_mul (Seq.index ci 4) zeta in
   let t1 = mont_mul (Seq.index ci 5) zeta in
   let t2 = mont_mul (Seq.index ci 6) zeta in
   let t3 = mont_mul (Seq.index ci 7) zeta in
   v (Seq.index co 0) == v (Seq.index ci 0) + v t0 /\
   v (Seq.index co 4) == v (Seq.index ci 0) - v t0 /\
   (v t0) % 8380417 == (v (Seq.index ci 4) * v zeta * 8265825) % 8380417 /\
   v (Seq.index co 1) == v (Seq.index ci 1) + v t1 /\
   v (Seq.index co 5) == v (Seq.index ci 1) - v t1 /\
   (v t1) % 8380417 == (v (Seq.index ci 5) * v zeta * 8265825) % 8380417 /\
   v (Seq.index co 2) == v (Seq.index ci 2) + v t2 /\
   v (Seq.index co 6) == v (Seq.index ci 2) - v t2 /\
   (v t2) % 8380417 == (v (Seq.index ci 6) * v zeta * 8265825) % 8380417 /\
   v (Seq.index co 3) == v (Seq.index ci 3) + v t3 /\
   v (Seq.index co 7) == v (Seq.index ci 3) - v t3 /\
   (v t3) % 8380417 == (v (Seq.index ci 7) * v zeta * 8265825) % 8380417)

(* Standalone: unfold one L2 opaque atom to the bridge's per-pair forall. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 100 --split_queries always --z3refresh"
let lemma_atom_to_bf_l2_avx2 (ci co: t_Array i32 (mk_usize 8))
      (zeta: i32{Spec.Utils.is_i32b 4190208 zeta})
    : Lemma (requires unit_post_l2_avx2 ci co zeta)
            (ensures
              (forall (p: nat{p < 4}).
                (let t = mont_mul (Seq.index ci (p+4)) zeta in
                 v (Seq.index co p)     == v (Seq.index ci p) + v t /\
                 v (Seq.index co (p+4)) == v (Seq.index ci p) - v t /\
                 (v t) % 8380417 == (v (Seq.index ci (p+4)) * v zeta * 8265825) % 8380417)))
  = reveal_opaque (`%unit_post_l2_avx2) unit_post_l2_avx2;
    introduce forall (p: nat{p < 4}).
        (let t = mont_mul (Seq.index ci (p+4)) zeta in
         v (Seq.index co p)     == v (Seq.index ci p) + v t /\
         v (Seq.index co (p+4)) == v (Seq.index ci p) - v t /\
         (v t) % 8380417 == (v (Seq.index ci (p+4)) * v zeta * 8265825) % 8380417)
    with (match p with | 0 -> () | 1 -> () | 2 -> () | _ -> ())
#pop-options

(* Per-chunk establishment: from input bound + 4 chunk ntt_step facts, build the
   opaque atom for chunk b AND the per-lane output bound. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 200 --split_queries always --z3refresh"
let lemma_l2_chunk_avx2
      (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (bnd:nat{bnd + 8380416 < pow2 31})
      (b: nat{b < 32})
    : Lemma
        (requires is_i32b_poly_avx2 bnd re /\ (forall (p:nat{p<4}). chunkfact_l2 re re_fut b p))
        (ensures
          unit_post_l2_avx2 (Seq.index (chunks_of_re_avx2 re) b) (Seq.index (chunks_of_re_avx2 re_fut) b)
            (mk_i32 (zeta_r (b + 32))) /\
          (forall (l:nat). l < 8 ==>
            Spec.Utils.is_i32b (bnd + 8380416) (to_i32x8 (Seq.index re_fut b).f_value (mk_u64 l))))
  = let h : squash (forall (p:nat{p<4}). chunkfact_l2 re re_fut b p) = () in
    eliminate forall (p:nat{p<4}). chunkfact_l2 re re_fut b p with 0;
    eliminate forall (p:nat{p<4}). chunkfact_l2 re re_fut b p with 1;
    eliminate forall (p:nat{p<4}). chunkfact_l2 re re_fut b p with 2;
    eliminate forall (p:nat{p<4}). chunkfact_l2 re re_fut b p with 3;
    lemma_l2_pair_relations re re_fut bnd b 0;
    lemma_l2_pair_relations re re_fut bnd b 1;
    lemma_l2_pair_relations re re_fut bnd b 2;
    lemma_l2_pair_relations re re_fut bnd b 3;
    reveal_opaque (`%unit_post_l2_avx2) unit_post_l2_avx2;
    introduce forall (l:nat{l<8}).
        Spec.Utils.is_i32b (bnd + 8380416) (to_i32x8 (Seq.index re_fut b).f_value (mk_u64 l))
    with (lemma_chunks_of_re_avx2_index re_fut b l)
#pop-options

(* Clean-context driver composition for L2: from the forall32 of opaque atoms,
   feed the Commute.Chunk poly lemma (ntt_layer mk_usize 2). *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 200 --split_queries always --z3refresh"
let lemma_l2_driver_compose_avx2
      (orig fut: t_Array (t_Array i32 (mk_usize 8)) (mk_usize 32))
    : Lemma
        (requires
          forall32 (fun b ->
            unit_post_l2_avx2 (Seq.index orig b) (Seq.index fut b)
              (mk_i32 (zeta_r (b + 32)))))
        (ensures
          (let in_flat = C.simd_units_to_array orig in
           let out_flat = C.simd_units_to_array fut in
           let spec = Hacspec_ml_dsa.Ntt.ntt_layer in_flat (mk_usize 2) in
           forall (i: nat). i < 256 ==>
             (v (Seq.index out_flat i)) % 8380417 == (v (Seq.index spec i)) % 8380417))
  = let zm (b: nat{b < 32}) : (z: i32{Spec.Utils.is_i32b 4190208 z}) =
      mk_i32 (zeta_r (b + 32)) in
    let t (b: nat{b < 32}) (p: nat{p < 4}) : i32 =
      mont_mul (Seq.index (Seq.index orig b) (p+4)) (zm b) in
    forall32_elim_1d (fun b -> unit_post_l2_avx2 (Seq.index orig b) (Seq.index fut b)
                                 (mk_i32 (zeta_r (b + 32))));
    (let aux_bf (b: nat{b < 32}) : Lemma
       (forall (p: nat{p < 4}).
         (let ci = Seq.index orig b in
          let co = Seq.index fut b in
          v (Seq.index co p)     == v (Seq.index ci p) + v (t b p) /\
          v (Seq.index co (p+4)) == v (Seq.index ci p) - v (t b p) /\
          (v (t b p)) % 8380417 == (v (Seq.index ci (p+4)) * v (zm b) * 8265825) % 8380417))
      = lemma_atom_to_bf_l2_avx2 (Seq.index orig b) (Seq.index fut b) (zm b)
     in Classical.forall_intro aux_bf);
    (let aux_z (b: nat{b < 32}) : Lemma
       ((v (zm b)) % 8380417 ==
        (v (Hacspec_ml_dsa.Ntt.v_ZETAS.[ mk_usize (b + 32) ] <: i32) * pow2 32) % 8380417)
      = reveal_opaque (`%Spec.MLDSA.Math.mod_q) (Spec.MLDSA.Math.mod_q);
        let _ = zeta_r (b + 32) in
        C.lemma_v_zetas_eq_zeta (b + 32)
     in Classical.forall_intro aux_z);
    C.lemma_ntt_layer_2_step_to_hacspec_poly orig fut t zm
#pop-options

(* FULL L2 body glue: from input bound + symbolic L2 post, derive output bound +
   functional congruence. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 200 --split_queries always --z3refresh"
let lemma_l2_full_avx2
      (orig_re re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (bnd:nat{bnd + 8380416 < pow2 31})
    : Lemma
        (requires is_i32b_poly_avx2 bnd orig_re /\ l2_post_sym orig_re re)
        (ensures
          is_i32b_poly_avx2 (bnd + 8380416) re /\
          (let in_flat = C.simd_units_to_array (chunks_of_re_avx2 orig_re) in
           let out_flat = C.simd_units_to_array (chunks_of_re_avx2 re) in
           let spec = Hacspec_ml_dsa.Ntt.ntt_layer in_flat (mk_usize 2) in
           forall (i: nat). i < 256 ==>
             (v (Seq.index out_flat i)) % 8380417 == (v (Seq.index spec i)) % 8380417))
  = lemma_chunkfacts_from_lift_l2 orig_re re;
    let aux (b:nat{b<32}) : Lemma
        (unit_post_l2_avx2 (Seq.index (chunks_of_re_avx2 orig_re) b) (Seq.index (chunks_of_re_avx2 re) b)
           (mk_i32 (zeta_r (b + 32)))
         /\ (forall (l:nat). l<8 ==>
              Spec.Utils.is_i32b (bnd + 8380416) (to_i32x8 (Seq.index re b).f_value (mk_u64 l))))
      = lemma_l2_chunk_avx2 orig_re re bnd b
    in Classical.forall_intro aux;
    lemma_is_i32b_poly_avx2_intro (bnd + 8380416) re;
    lemma_l2_driver_compose_avx2 (chunks_of_re_avx2 orig_re) (chunks_of_re_avx2 re)
#pop-options

(* Bridge: literal-zeta L2 post (l2_post) implies symbolic-zeta form (l2_post_sym).
   32 zeta_r literal assert_norms (idx 32..63, all of zeta_r(32+i*2)/zeta_r(32+i*2+1)). *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"
let lemma_l2post_to_sym (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Lemma (requires l2_post re re_fut) (ensures l2_post_sym re re_fut)
  =
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 32 == 2706023);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 33 == 95776);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 34 == 3077325);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 35 == 3530437);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 36 == (- 1661693));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 37 == (- 3592148));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 38 == (- 2537516));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 39 == 3915439);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 40 == (- 3861115));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 41 == (- 3043716));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 42 == 3574422);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 43 == (- 2867647));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 44 == 3539968);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 45 == (- 300467));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 46 == 2348700);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 47 == (- 539299));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 48 == (- 1699267));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 49 == (- 1643818));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 50 == 3505694);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 51 == (- 3821735));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 52 == 3507263);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 53 == (- 2140649));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 54 == (- 1600420));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 55 == 3699596);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 56 == 811944);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 57 == 531354);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 58 == 954230);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 59 == 3881043);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 60 == 3900724);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 61 == (- 2556880));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 62 == 2071892);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 63 == (- 2797779))
#pop-options
(* ===================================================================== *)
(* ============================ LAYER 1 ================================= *)
(* ===================================================================== *)
(* L1 (len=2, within-chunk): per chunk b, TWO zetas (one per half h in {0,1}).
   The 4 butterflies act on lane pairs indexed by p in 0..3 with
   h = p/2, j' = p%2, lanes (4h+j', 4h+j'+2).  Zeta for half h of chunk b is
   zeta_r (2*b + h + 64).  The Commute bridge consumes the (b,h,j') indexing;
   we collapse (h,j') to p (p/2=h, p%2=j') so reindex_32_from_16 applies. *)

(* The post's j0-match equals the clean formula 4*(j/2)+(j%2). *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 30"
let lemma_j0_l1 (j:nat{j<4})
    : Lemma ((match j with | 0 -> 0 | 1 -> 1 | 2 -> 4 | _ -> 5) == 4*(j/2)+(j%2))
  = (match j with | 0 -> () | 1 -> () | 2 -> () | _ -> ())
#pop-options

(* CRUX (genuinely-new AVX2 logic for L1): from the per-(b,p) ntt_step post +
   zeta bound + input bound, derive the butterfly relations the L1 bridge
   consumes.  Lane pair (4h+j', 4h+j'+2) with h=p/2,j'=p%2; zeta_r(2b+h+64). *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"
let lemma_l1_pair_relations
      (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (bnd:nat{bnd + 8380416 < pow2 31})
      (b: nat{b < 32}) (p: nat{p < 4})
    : Lemma
        (requires
          is_i32b_poly_avx2 bnd re /\
          (let ci = chunks_of_re_avx2 re in
           let co = chunks_of_re_avx2 re_fut in
           let lo : nat = 4*(p/2)+(p%2) in
           (Seq.index (Seq.index co b) lo, Seq.index (Seq.index co b) (lo+2)) ==
             ntt_step (mk_int (zeta_r (2*b + p/2 + 64)))
               (Seq.index (Seq.index ci b) lo, Seq.index (Seq.index ci b) (lo+2))))
        (ensures
          (let ci = chunks_of_re_avx2 re in
           let co = chunks_of_re_avx2 re_fut in
           let lo : nat = 4*(p/2)+(p%2) in
           let z : i32 = Hacspec_ml_dsa.Ntt.v_ZETAS.[ mk_usize (2*b + p/2 + 64) ] in
           let zm : i32 = mk_int (zeta_r (2*b + p/2 + 64)) in
           let t : i32 = mont_mul (Seq.index (Seq.index ci b) (lo+2)) zm in
           v (Seq.index (Seq.index co b) lo)     == v (Seq.index (Seq.index ci b) lo) + v t /\
           v (Seq.index (Seq.index co b) (lo+2)) == v (Seq.index (Seq.index ci b) lo) - v t /\
           (v t) % 8380417 ==
             (v (Seq.index (Seq.index ci b) (lo+2)) * v zm * 8265825) % 8380417 /\
           (v zm) % 8380417 == (v z * pow2 32) % 8380417 /\
           Spec.Utils.is_i32b (bnd + 8380416) (Seq.index (Seq.index co b) lo) /\
           Spec.Utils.is_i32b (bnd + 8380416) (Seq.index (Seq.index co b) (lo+2))))
  = let ci = chunks_of_re_avx2 re in
    let co = chunks_of_re_avx2 re_fut in
    let lo : nat = 4*(p/2)+(p%2) in
    assert (lo < 6);
    let ci_lo = Seq.index (Seq.index ci b) lo in
    let ci_hi = Seq.index (Seq.index ci b) (lo+2) in
    let co_lo = Seq.index (Seq.index co b) lo in
    let co_hi = Seq.index (Seq.index co b) (lo+2) in
    let zm : i32 = mk_int (zeta_r (2*b + p/2 + 64)) in
    let t : i32 = mont_mul ci_hi zm in
    // ntt_step unfolds (non-opaque):
    assert (co_lo == add_mod_opaque ci_lo t);
    assert (co_hi == sub_mod_opaque ci_lo t);
    // input bound on ci_lo (via the opaque-predicate elim)
    lemma_chunks_of_re_avx2_index re b lo;
    lemma_is_i32b_poly_avx2_elim bnd re b lo;
    assert (Spec.Utils.is_i32b bnd ci_lo);
    // mont bound + mod-q (zeta_r bounded by 4190208 < FIELD_MAX)
    assert (Spec.Utils.is_i32b 8380416 zm);
    C.lemma_mont_mul_bound_and_mod_q ci_hi zm;
    assert (Spec.Utils.is_i32b 8380416 t);
    // add/sub exactness (no overflow)
    Spec.Intrinsics.reveal_opaque_arithmetic_ops #i32_inttype;
    assert (v co_lo == v ci_lo + v t);
    assert (v co_hi == v ci_lo - v t);
    // zeta canonicalization
    let idx : nat = 2*b + p/2 + 64 in
    C.lemma_v_zetas_eq_zeta idx
#pop-options

(* L1 verbatim post (literal-zeta, matches ntt_at_layer_1_'s ensures). *)
unfold let l1_post (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32)) : Type0 =
  norm [
      primops; iota;
      delta_namespace [`%zeta_r; `%Spec.Utils.forall4; `%Spec.Utils.forall16]
    ]
    (Spec.Utils.forall16 (fun i ->
          let nre = re_fut in
          let re0 = Seq.index re (i * 2) in
          let re1 = Seq.index re (i * 2 + 1) in
          let nre0 = Seq.index nre (i * 2) in
          let nre1 = Seq.index nre (i * 2 + 1) in
          Spec.Utils.forall4 (fun j ->
                let zeta0 = zeta_r (64 + i * 4 + j / 2) in
                let zeta1 = zeta_r (64 + i * 4 + j / 2 + 2) in
                let j0 = (match j with | 0 -> 0 | 1 -> 1 | 2 -> 4 | _ -> 5) in
                let j1 = j0 + 2 in
                (to_i32x8 nre0.f_value (mk_u64 j0), to_i32x8 nre0.f_value (mk_u64 j1)) ==
                ntt_step (mk_int zeta0)
                  (to_i32x8 re0.f_value (mk_u64 j0), to_i32x8 re0.f_value (mk_u64 j1)) /\
                (to_i32x8 nre1.f_value (mk_u64 j0), to_i32x8 nre1.f_value (mk_u64 j1)) ==
                ntt_step (mk_int zeta1)
                  (to_i32x8 re1.f_value (mk_u64 j0), to_i32x8 re1.f_value (mk_u64 j1)))))

(* Per-(b,p) chunk ntt_step fact: lane pair (lo, lo+2), zeta_r(2b+p/2+64). *)
unfold let chunkfact_l1 (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
                        (b:nat{b<32}) (p:nat{p<4}) : Type0 =
  let ci = chunks_of_re_avx2 re in
  let co = chunks_of_re_avx2 re_fut in
  let lo : nat = 4*(p/2)+(p%2) in
  (Seq.index (Seq.index co b) lo, Seq.index (Seq.index co b) (lo+2)) ==
    ntt_step (mk_int (zeta_r (2*b + p/2 + 64)))
      (Seq.index (Seq.index ci b) lo, Seq.index (Seq.index ci b) (lo+2))

(* Symbolic L1 post (zeta_r NOT norm-evaluated). *)
unfold let l1_post_sym (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32)) : Type0 =
  norm [
      primops; iota;
      delta_namespace [`%Spec.Utils.forall4; `%Spec.Utils.forall16]
    ]
    (Spec.Utils.forall16 (fun i ->
          let nre = re_fut in
          let re0 = Seq.index re (i * 2) in
          let re1 = Seq.index re (i * 2 + 1) in
          let nre0 = Seq.index nre (i * 2) in
          let nre1 = Seq.index nre (i * 2 + 1) in
          Spec.Utils.forall4 (fun j ->
                let zeta0 = zeta_r (64 + i * 4 + j / 2) in
                let zeta1 = zeta_r (64 + i * 4 + j / 2 + 2) in
                let j0 = (match j with | 0 -> 0 | 1 -> 1 | 2 -> 4 | _ -> 5) in
                let j1 = j0 + 2 in
                (to_i32x8 nre0.f_value (mk_u64 j0), to_i32x8 nre0.f_value (mk_u64 j1)) ==
                ntt_step (mk_int zeta0)
                  (to_i32x8 re0.f_value (mk_u64 j0), to_i32x8 re0.f_value (mk_u64 j1)) /\
                (to_i32x8 nre1.f_value (mk_u64 j0), to_i32x8 nre1.f_value (mk_u64 j1)) ==
                ntt_step (mk_int zeta1)
                  (to_i32x8 re1.f_value (mk_u64 j0), to_i32x8 re1.f_value (mk_u64 j1)))))

unfold let l1_body (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
                   (i:nat{i<16}) : Type0 =
  let re0 = Seq.index re (i*2) in
  let re1 = Seq.index re (i*2+1) in
  let nre0 = Seq.index re_fut (i*2) in
  let nre1 = Seq.index re_fut (i*2+1) in
  Spec.Utils.forall4 (fun j ->
        let zeta0 = zeta_r (64 + i*4 + j/2) in
        let zeta1 = zeta_r (64 + i*4 + j/2 + 2) in
        let j0 = (match j with | 0 -> 0 | 1 -> 1 | 2 -> 4 | _ -> 5) in let j1 = j0+2 in
        (to_i32x8 nre0.f_value (mk_u64 j0), to_i32x8 nre0.f_value (mk_u64 j1)) ==
          ntt_step (mk_int zeta0) (to_i32x8 re0.f_value (mk_u64 j0), to_i32x8 re0.f_value (mk_u64 j1)) /\
        (to_i32x8 nre1.f_value (mk_u64 j0), to_i32x8 nre1.f_value (mk_u64 j1)) ==
          ntt_step (mk_int zeta1) (to_i32x8 re1.f_value (mk_u64 j0), to_i32x8 re1.f_value (mk_u64 j1)))

(* l1_post_sym ==> forall i<16. l1_body i  (reuse shared forall16_elim_1d). *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 60"
let lemma_lift_l1 (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Lemma (requires l1_post_sym re re_fut)
            (ensures forall (i:nat{i<16}). l1_body re re_fut i)
  = forall16_elim_1d (l1_body re re_fut)
#pop-options

unfold let body2_l1 (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
                    (i:nat{i<16}) (j:nat{j<4}) : Type0 =
  let re0 = Seq.index re (i*2) in
  let re1 = Seq.index re (i*2+1) in
  let nre0 = Seq.index re_fut (i*2) in
  let nre1 = Seq.index re_fut (i*2+1) in
  let zeta0 = zeta_r (64 + i*4 + j/2) in
  let zeta1 = zeta_r (64 + i*4 + j/2 + 2) in
  let j0 = (match j with | 0 -> 0 | 1 -> 1 | 2 -> 4 | _ -> 5) in let j1 = j0+2 in
  (to_i32x8 nre0.f_value (mk_u64 j0), to_i32x8 nre0.f_value (mk_u64 j1)) ==
    ntt_step (mk_int zeta0) (to_i32x8 re0.f_value (mk_u64 j0), to_i32x8 re0.f_value (mk_u64 j1)) /\
  (to_i32x8 nre1.f_value (mk_u64 j0), to_i32x8 nre1.f_value (mk_u64 j1)) ==
    ntt_step (mk_int zeta1) (to_i32x8 re1.f_value (mk_u64 j0), to_i32x8 re1.f_value (mk_u64 j1))

(* l1_body i is definitionally forall4 (fun j -> body2_l1 i j); lift to forall i j. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 80"
let lemma_lift2_l1 (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Lemma (requires l1_post_sym re re_fut)
            (ensures forall (i:nat{i<16}) (j:nat{j<4}). body2_l1 re re_fut i j)
  = lemma_lift_l1 re re_fut;
    let aux (i:nat{i<16}) : Lemma (forall (j:nat{j<4}). body2_l1 re re_fut i j) =
      forall4_elim_1d (fun (j:nat{j<4}) -> body2_l1 re re_fut i j)
    in Classical.forall_intro aux
#pop-options

(* Even chunk b=2i: chunkfact_l1 (2i) p from body2_l1 i p's nre0 part.
   The post's j0 = 4*(p/2)+(p%2) = lo; zeta_r(64+4i+p/2) = zeta_r(2*(2i)+p/2+64). *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"
let lemma_chunkfact_l1_even
      (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (i:nat{i<16}) (p:nat{p<4})
    : Lemma (requires body2_l1 re re_fut i p) (ensures chunkfact_l1 re re_fut (2*i) p)
  = lemma_j0_l1 p;
    let lo : nat = 4*(p/2)+(p%2) in
    lemma_chunks_of_re_avx2_index re (2*i) lo;
    lemma_chunks_of_re_avx2_index re (2*i) (lo+2);
    lemma_chunks_of_re_avx2_index re_fut (2*i) lo;
    lemma_chunks_of_re_avx2_index re_fut (2*i) (lo+2)
#pop-options

(* Odd chunk b=2i+1: chunkfact_l1 (2i+1) p from body2_l1 i p's nre1 part.
   zeta_r(64+4i+p/2+2) = zeta_r(2*(2i+1)+p/2+64). *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"
let lemma_chunkfact_l1_odd
      (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (i:nat{i<16}) (p:nat{p<4})
    : Lemma (requires body2_l1 re re_fut i p) (ensures chunkfact_l1 re re_fut (2*i+1) p)
  = lemma_j0_l1 p;
    let lo : nat = 4*(p/2)+(p%2) in
    lemma_chunks_of_re_avx2_index re (2*i+1) lo;
    lemma_chunks_of_re_avx2_index re (2*i+1) (lo+2);
    lemma_chunks_of_re_avx2_index re_fut (2*i+1) lo;
    lemma_chunks_of_re_avx2_index re_fut (2*i+1) (lo+2)
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"
let lemma_chunkfacts_from_lift_l1
      (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Lemma (requires l1_post_sym re re_fut)
            (ensures forall (b:nat{b<32}) (p:nat{p<4}). chunkfact_l1 re re_fut b p)
  = lemma_lift2_l1 re re_fut;
    let auxe (i:nat{i<16}) (p:nat{p<4}) : Lemma (chunkfact_l1 re re_fut (2*i) p) =
      lemma_chunkfact_l1_even re re_fut i p
    in Classical.forall_intro_2 auxe;
    let auxo (i:nat{i<16}) (p:nat{p<4}) : Lemma (chunkfact_l1 re re_fut (2*i+1) p) =
      lemma_chunkfact_l1_odd re re_fut i p
    in Classical.forall_intro_2 auxo;
    reindex_32_from_16 (chunkfact_l1 re re_fut)
#pop-options

(* L1 opaque per-chunk FE atom: TWO zetas (one per half h), pairs (4h+j',4h+j'+2).
   Mirror of Portable unit_fe_post_l1 with mont_mul.  Lane layout:
   half 0 -> pairs (0,2),(1,3) with zeta0; half 1 -> pairs (4,6),(5,7) with zeta1. *)
[@@ "opaque_to_smt"]
let unit_post_l1_avx2 (ci co: t_Array i32 (mk_usize 8))
      (zeta0 zeta1: i32{Spec.Utils.is_i32b 4190208 zeta0 /\ Spec.Utils.is_i32b 4190208 zeta1}) : Type0 =
  (let t00 = mont_mul (Seq.index ci 2) zeta0 in
   let t01 = mont_mul (Seq.index ci 3) zeta0 in
   let t10 = mont_mul (Seq.index ci 6) zeta1 in
   let t11 = mont_mul (Seq.index ci 7) zeta1 in
   v (Seq.index co 0) == v (Seq.index ci 0) + v t00 /\
   v (Seq.index co 2) == v (Seq.index ci 0) - v t00 /\
   (v t00) % 8380417 == (v (Seq.index ci 2) * v zeta0 * 8265825) % 8380417 /\
   v (Seq.index co 1) == v (Seq.index ci 1) + v t01 /\
   v (Seq.index co 3) == v (Seq.index ci 1) - v t01 /\
   (v t01) % 8380417 == (v (Seq.index ci 3) * v zeta0 * 8265825) % 8380417 /\
   v (Seq.index co 4) == v (Seq.index ci 4) + v t10 /\
   v (Seq.index co 6) == v (Seq.index ci 4) - v t10 /\
   (v t10) % 8380417 == (v (Seq.index ci 6) * v zeta1 * 8265825) % 8380417 /\
   v (Seq.index co 5) == v (Seq.index ci 5) + v t11 /\
   v (Seq.index co 7) == v (Seq.index ci 5) - v t11 /\
   (v t11) % 8380417 == (v (Seq.index ci 7) * v zeta1 * 8265825) % 8380417)

(* Standalone: unfold one L1 opaque atom to the bridge's per-(h,j) forall. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 100 --split_queries always --z3refresh"
let lemma_atom_to_bf_l1_avx2 (ci co: t_Array i32 (mk_usize 8))
      (zf: (h: nat{h < 2}) -> (z: i32{Spec.Utils.is_i32b 4190208 z}))
    : Lemma (requires unit_post_l1_avx2 ci co (zf 0) (zf 1))
            (ensures
              (forall (h: nat{h < 2}) (j: nat{j < 2}).
                (let t = mont_mul (Seq.index ci (4*h+j+2)) (zf h) in
                 v (Seq.index co (4*h+j))   == v (Seq.index ci (4*h+j)) + v t /\
                 v (Seq.index co (4*h+j+2)) == v (Seq.index ci (4*h+j)) - v t /\
                 (v t) % 8380417 == (v (Seq.index ci (4*h+j+2)) * v (zf h) * 8265825) % 8380417)))
  = reveal_opaque (`%unit_post_l1_avx2) unit_post_l1_avx2;
    introduce forall (h: nat{h < 2}) (j: nat{j < 2}).
        (let t = mont_mul (Seq.index ci (4*h+j+2)) (zf h) in
         v (Seq.index co (4*h+j))   == v (Seq.index ci (4*h+j)) + v t /\
         v (Seq.index co (4*h+j+2)) == v (Seq.index ci (4*h+j)) - v t /\
         (v t) % 8380417 == (v (Seq.index ci (4*h+j+2)) * v (zf h) * 8265825) % 8380417)
    with (match h with | 0 -> (match j with | 0 -> () | _ -> ()) | _ -> (match j with | 0 -> () | _ -> ()))
#pop-options

(* Generic createi-free dispatch: plain forall over p<4 -> 4 ground facts.
   ABSTRACT q so no chunkfact/createi term enters this VC (the chunkfact_l1
   body's p/2,p%2 lane formula is a poor SMT trigger; this forces the 4
   instances by ground match). *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 40"
let forall4_inst (q: (p:nat{p<4}) -> Type0)
    : Lemma (requires forall (p:nat{p<4}). q p)
            (ensures q 0 /\ q 1 /\ q 2 /\ q 3)
  = ()
#pop-options

(* Per-chunk establishment: from input bound + 4 chunk ntt_step facts, build the
   L1 opaque atom for chunk b AND the per-lane output bound.  Maps the (b,p)
   chunkfacts (p in 0..3) to the atom's (h,j') lane pairs. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 200 --split_queries always --z3refresh"
let lemma_l1_chunk_avx2
      (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (bnd:nat{bnd + 8380416 < pow2 31})
      (b: nat{b < 32})
    : Lemma
        (requires is_i32b_poly_avx2 bnd re /\ (forall (p:nat{p<4}). chunkfact_l1 re re_fut b p))
        (ensures
          unit_post_l1_avx2 (Seq.index (chunks_of_re_avx2 re) b) (Seq.index (chunks_of_re_avx2 re_fut) b)
            (mk_i32 (zeta_r (2*b + 0 + 64))) (mk_i32 (zeta_r (2*b + 1 + 64))) /\
          (forall (l:nat). l < 8 ==>
            Spec.Utils.is_i32b (bnd + 8380416) (to_i32x8 (Seq.index re_fut b).f_value (mk_u64 l))))
  = // materialize the chunkfact hypothesis at each literal p (createi-free dispatch)
    forall4_inst (chunkfact_l1 re re_fut b);
    lemma_l1_pair_relations re re_fut bnd b 0;
    lemma_l1_pair_relations re re_fut bnd b 1;
    lemma_l1_pair_relations re re_fut bnd b 2;
    lemma_l1_pair_relations re re_fut bnd b 3;
    reveal_opaque (`%unit_post_l1_avx2) unit_post_l1_avx2;
    introduce forall (l:nat{l<8}).
        Spec.Utils.is_i32b (bnd + 8380416) (to_i32x8 (Seq.index re_fut b).f_value (mk_u64 l))
    with (lemma_chunks_of_re_avx2_index re_fut b l)
#pop-options

(* Clean-context driver composition for L1: from forall32 of opaque atoms, feed
   the Commute.Chunk L1 poly lemma.  Mirror of Portable lemma_l1_driver_compose
   with mont_mul + the AVX2 atom + the SEPARATE zeta-cong forall. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 200 --split_queries always --z3refresh"
let lemma_l1_driver_compose_avx2
      (orig fut: t_Array (t_Array i32 (mk_usize 8)) (mk_usize 32))
    : Lemma
        (requires
          forall32 (fun b ->
            unit_post_l1_avx2 (Seq.index orig b) (Seq.index fut b)
              (mk_i32 (zeta_r (2*b + 0 + 64))) (mk_i32 (zeta_r (2*b + 1 + 64)))))
        (ensures
          (let in_flat = C.simd_units_to_array orig in
           let out_flat = C.simd_units_to_array fut in
           let spec = Hacspec_ml_dsa.Ntt.ntt_layer in_flat (mk_usize 1) in
           forall (i: nat). i < 256 ==>
             (v (Seq.index out_flat i)) % 8380417 == (v (Seq.index spec i)) % 8380417))
  = let zm (b: nat{b < 32}) (h: nat{h < 2}) : (z: i32{Spec.Utils.is_i32b 4190208 z}) =
      mk_i32 (zeta_r (2*b + h + 64)) in
    let t (b: nat{b < 32}) (h: nat{h < 2}) (j: nat{j < 2}) : i32 =
      mont_mul (Seq.index (Seq.index orig b) (4*h+j+2)) (zm b h) in
    forall32_elim_1d (fun b -> unit_post_l1_avx2 (Seq.index orig b) (Seq.index fut b)
                                 (mk_i32 (zeta_r (2*b + 0 + 64))) (mk_i32 (zeta_r (2*b + 1 + 64))));
    (let aux_bf (b: nat{b < 32}) : Lemma
       (forall (h: nat{h < 2}) (j: nat{j < 2}).
         (let ci = Seq.index orig b in
          let co = Seq.index fut b in
          v (Seq.index co (4*h+j))   == v (Seq.index ci (4*h+j)) + v (t b h j) /\
          v (Seq.index co (4*h+j+2)) == v (Seq.index ci (4*h+j)) - v (t b h j) /\
          (v (t b h j)) % 8380417 == (v (Seq.index ci (4*h+j+2)) * v (zm b h) * 8265825) % 8380417))
      = lemma_atom_to_bf_l1_avx2 (Seq.index orig b) (Seq.index fut b) (fun h -> zm b h)
     in Classical.forall_intro aux_bf);
    (let aux_z (b: nat{b < 32}) (h: nat{h < 2}) : Lemma
       ((v (zm b h)) % 8380417 ==
        (v (Hacspec_ml_dsa.Ntt.v_ZETAS.[ mk_usize (2*b + h + 64) ] <: i32) * pow2 32) % 8380417)
      = reveal_opaque (`%Spec.MLDSA.Math.mod_q) (Spec.MLDSA.Math.mod_q);
        let _ = zeta_r (2*b + h + 64) in
        C.lemma_v_zetas_eq_zeta (2*b + h + 64)
     in Classical.forall_intro_2 aux_z);
    C.lemma_ntt_layer_1_step_to_hacspec_poly orig fut t zm
#pop-options

(* FULL L1 body glue: from input bound + symbolic L1 post, derive the complete
   layer-fn post (output bound + functional congruence to ntt_layer .. (mk_usize 1)). *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 200 --split_queries always --z3refresh"
let lemma_l1_full_avx2
      (orig_re re: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
      (bnd:nat{bnd + 8380416 < pow2 31})
    : Lemma
        (requires is_i32b_poly_avx2 bnd orig_re /\ l1_post_sym orig_re re)
        (ensures
          is_i32b_poly_avx2 (bnd + 8380416) re /\
          (let in_flat = C.simd_units_to_array (chunks_of_re_avx2 orig_re) in
           let out_flat = C.simd_units_to_array (chunks_of_re_avx2 re) in
           let spec = Hacspec_ml_dsa.Ntt.ntt_layer in_flat (mk_usize 1) in
           forall (i: nat). i < 256 ==>
             (v (Seq.index out_flat i)) % 8380417 == (v (Seq.index spec i)) % 8380417))
  = lemma_chunkfacts_from_lift_l1 orig_re re;
    let aux (b:nat{b<32}) : Lemma
        (unit_post_l1_avx2 (Seq.index (chunks_of_re_avx2 orig_re) b) (Seq.index (chunks_of_re_avx2 re) b)
           (mk_i32 (zeta_r (2*b + 0 + 64))) (mk_i32 (zeta_r (2*b + 1 + 64)))
         /\ (forall (l:nat). l<8 ==>
              Spec.Utils.is_i32b (bnd + 8380416) (to_i32x8 (Seq.index re b).f_value (mk_u64 l))))
      = lemma_l1_chunk_avx2 orig_re re bnd b
    in Classical.forall_intro aux;
    lemma_is_i32b_poly_avx2_intro (bnd + 8380416) re;
    lemma_l1_driver_compose_avx2 (chunks_of_re_avx2 orig_re) (chunks_of_re_avx2 re)
#pop-options

(* Bridge: literal-zeta L1 post (l1_post) implies symbolic-zeta form (l1_post_sym).
   L1 chunk zetas are zeta_r(2b+h+64), b=0..31,h=0..1 -> idx 64..127 (64 literals). *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"
let lemma_l1post_to_sym (re re_fut: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
    : Lemma (requires l1_post re re_fut) (ensures l1_post_sym re re_fut)
  =
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 64 == (- 3930395));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 65 == (- 1528703));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 66 == (- 3677745));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 67 == (- 3041255));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 68 == (- 1452451));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 69 == 3475950);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 70 == 2176455);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 71 == (- 1585221));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 72 == (- 1257611));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 73 == 1939314);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 74 == (- 4083598));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 75 == (- 1000202));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 76 == (- 3190144));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 77 == (- 3157330));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 78 == (- 3632928));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 79 == 126922);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 80 == 3412210);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 81 == (- 983419));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 82 == 2147896);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 83 == 2715295);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 84 == (- 2967645));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 85 == (- 3693493));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 86 == (- 411027));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 87 == (- 2477047));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 88 == (- 671102));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 89 == (- 1228525));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 90 == (- 22981));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 91 == (- 1308169));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 92 == (- 381987));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 93 == 1349076);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 94 == 1852771);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 95 == (- 1430430));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 96 == (- 3343383));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 97 == 264944);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 98 == 508951);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 99 == 3097992);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 100 == 44288);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 101 == (- 1100098));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 102 == 904516);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 103 == 3958618);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 104 == (- 3724342));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 105 == (- 8578));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 106 == 1653064);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 107 == (- 3249728));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 108 == 2389356);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 109 == (- 210977));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 110 == 759969);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 111 == (- 1316856));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 112 == 189548);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 113 == (- 3553272));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 114 == 3159746);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 115 == (- 1851402));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 116 == (- 2409325));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 117 == (- 177440));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 118 == 1315589);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 119 == 1341330);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 120 == 1285669);
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 121 == (- 1584928));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 122 == (- 812732));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 123 == (- 1439742));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 124 == (- 3019102));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 125 == (- 3881060));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 126 == (- 3628969));
    assert_norm (Spec.MLDSA.NttConstants.zeta_r 127 == 3839961)
#pop-options
#pop-options
