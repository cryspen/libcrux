module Libcrux_intrinsics.Arm64_ml_kem_views
#set-options "--fuel 0 --ifuel 1 --z3rlimit 50"
open FStar.Mul
open Core_models
open Libcrux_intrinsics.Arm64

(* ============================================================================
   ml-kem NEON lane-view + per-op fact companion (core-models migration, WS C).

   The ARM/NEON analog of `Libcrux_intrinsics.Avx2_ml_kem_views`.  It exposes to
   ml-kem's NEON proofs the lane VIEWS (`vec128_as_i16x8` / `get_lane_i16x8` /
   ...) and per-op FACT lemmas that the hand-written pcm
   `Libcrux_intrinsics.Arm64_extract` interface carried as op `ensures`, now
   phrased over the REAL `Libcrux_intrinsics.Arm64` ops (which delegate to the
   differentially-tested `libcrux-core-models` NEON model).

   TRUST.  The Seq lane view is a per-index read of the canonical core-models
   FunArray codec (`Canon.to_i16x8` = `Int_vec_interp` width 128), and every
   op-fact is PROVEN from the canonical NEON op-lemma set in
   `Libcrux_core_models.Neon_views` (which rests only on the differentially
   tested `Arm.Interpretations.Int_vec.Lemmas` lifts + the PROVEN codec
   round-trip).  Under pcm these facts were assumed op `ensures`; the trust
   surface here has strictly SHRUNK.  NO fact in this module is assumed.

   STATUS (WIP — cm-migration, 2026-08-08).  This file currently carries the
   VALIDATED "arithmetic backbone": the structural i16x8 lane view + the pure
   per-lane arithmetic/transpose op-facts (`vadd/vsub/vmul/vmul_n_s16`,
   `vtrn1q/vtrn2q_s16`), which prove directly from the `Neon_views` codec
   op-lemmas (`ArmIV.OP` is a per-lane FunArray op, so `Seq.init`/`map2 f
   (view a) (view b)` matches by `Seq.lemma_eq_intro`).

   REMAINING (next sessions), by tier — each needs a companion op-fact and, where
   noted, a FOUNDATION lemma in `Neon_views` (width-128 analog of an existing
   `Intrinsics_views` width-256 lemma):
     * Logical (vand/veor/vbic/veor3/vbcax): `ArmIV.OP` is a BIT-LEVEL
       `impl_9__from_fn 128`, so needs the codec-commute lemma
       `to_i16x8 (bitop a b) [i] == (view a)[i] `op` (view b)[i]` — the width-128
       analog of `Intrinsics_views.lemma_{and,xor}_i16x16_iv` (which rests on
       `lemma_from_fn_lane_reader`/`lemma_bv_index`, both hardcoded to 256; port
       to 128 in `Neon_views`).
     * Shifts (vshrq_n / vshlq_n family): per-lane shift codec facts (ArmIV shift body).
     * Clamp (vqdmulhq_s16 / _n_s16 / _n_s32): saturating-clamp per-lane facts.
     * trn: s16 (vtrn1q/vtrn2q_s16) DONE; s32/s64/u64 remaining — pure mirror
       (ArmIV.trn on codec), like the arithmetic ops; need the i32x4/i64x2/u64x2
       views added here.
     * Reinterpret same-width (s16<->u16, s32<->u32): `result == a` (bit-identity
       `ArmIV.OP a == a`) + per-lane cast_mod codec-signedness fact.
     * Reinterpret cross-width (s32<->s16, s64<->s16, u32<->u8, u16<->u8): the
       HARD tier — `result == a` + a codec-repack lemma relating the two views of
       the same 128 bits (`i16x2_as_i32` / `i64_i16lane` / ...).  These are pure
       codec facts (independent of any op); prove via composed `Canon.lemma_readback`.
     * mull/mlal/get_low/high/addv (i16x4<->i32x4 halves): various.
     * load/store/dup (vld1q / vst1q / vdupq_n family): `Arm.Extra` slice-model facts.
     * The bit bridge `bit_vec_of_int_t_array_vec128_as_i16x8_lemma` (used by
       from_bytes/to_bytes): mirror `Avx2_ml_kem_views.bit_vec_of_int_t_array_
       vec128_as_i16x8_lemma` (one `Canon.lemma_readback` call).
     * Helper lets (`i16_bits_as_u32`, `u32_lo16_as_i16`, `i16x2_as_i32`,
       `i64_i16lane`, `arm_sshl_i16`, ...) re-exported verbatim from the pcm
       `Arm64_extract.fsti` (referenced by the reinterpret facts + consumer
       proofs).

   Lives in `proofs/fstar/spec/` (hand-maintained, NOT the hax-extraction dir),
   so `cargo hax into` never clobbers it; on ml-kem's include path only.  It is
   NOT a make ROOT — it verifies only as a dependency once the NEON consumers are
   repointed (`Arm64_extract.X` -> `Arm64_ml_kem_views.X`) and lib.rs is flipped.
   ========================================================================== *)

module Funarr = Libcrux_core_models.Abstractions.Funarr
module BV     = Libcrux_core_models.Abstractions.Bitvec
module Canon  = Libcrux_core_models.Intrinsics_views
module NV     = Libcrux_core_models.Neon_views
module ArmIV  = Libcrux_core_models.Core_arch.Arm.Interpretations.Int_vec

(* ── Lane-view types (mirror the pcm `t_e_*` abstract vector types) ────────── *)
unfold type t_e_int16x8_t  = BV.t_BitVec (mk_u64 128)
unfold type t_e_int32x4_t  = BV.t_BitVec (mk_u64 128)
unfold type t_e_uint32x4_t = BV.t_BitVec (mk_u64 128)
unfold type t_e_uint16x8_t = BV.t_BitVec (mk_u64 128)
unfold type t_e_uint8x16_t = BV.t_BitVec (mk_u64 128)
unfold type t_e_int64x2_t  = BV.t_BitVec (mk_u64 128)
unfold type t_e_uint64x2_t = BV.t_BitVec (mk_u64 128)
unfold type t_e_int16x4_t  = BV.t_BitVec (mk_u64 64)
unfold type t_e_uint16x4_t = BV.t_BitVec (mk_u64 64)

(* ── i16x8 lane view (A-on-B adapter over canonical to_i16x8).  OPAQUE for the
      same reasons as x86's `vec256_as_i16x16`: keeps pcm's abstraction (still
      PROVEN, not assumed); the ONLY route to the codec is `vec128_index`. ──── *)
[@@ "opaque_to_smt"]
let vec128_as_i16x8 (x: t_e_int16x8_t) : t_Array i16 (sz 8) =
  Seq.init 8 (fun i -> Funarr.impl_5__get (mk_u64 8) #i16 (Canon.to_i16x8 x) (mk_u64 i))
let get_lane_i16x8 (v: t_e_int16x8_t) (i: nat{i < 8}) : i16 = Seq.index (vec128_as_i16x8 v) i

let vec128_index (x: t_e_int16x8_t) (i: nat{i < 8})
  : Lemma (Seq.index (vec128_as_i16x8 x) i
           == Funarr.impl_5__get (mk_u64 8) #i16 (Canon.to_i16x8 x) (mk_u64 i))
          [SMTPat (Seq.index (vec128_as_i16x8 x) i)]
  = reveal_opaque (`%vec128_as_i16x8) vec128_as_i16x8

let vec128_as_i16x8_len (x: t_e_int16x8_t)
  : Lemma (Seq.length (vec128_as_i16x8 x) == 8)
          [SMTPat (Seq.length (vec128_as_i16x8 x))]
  = ()

let vec128_as_i16x8_slice_ok (x: t_e_int16x8_t)
  : Lemma (Seq.length (vec128_as_i16x8 x) <= Rust_primitives.Integers.max_usize)
          [SMTPat (vec128_as_i16x8 x)]
  = assert_norm (8 <= Rust_primitives.Integers.max_usize)

(* ── i16x8 arithmetic op-facts (VALIDATED backbone) ───────────────────────────
   Each mirrors `Avx2_ml_kem_views.lemma_mm256_add_epi16`: the real op delegates
   to `Neon.OP` (transparent), `NV.lemma_OP` gives `to_i16x8 (Neon.OP a b) ==
   ArmIV.OP (to_i16x8 a) (to_i16x8 b)`, `ArmIV.OP` is a per-lane FunArray op, so
   `Seq.lemma_eq_intro` closes against `Spec.Utils.map2`. ────────────────────── *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vaddq_s16 (a b: t_e_int16x8_t)
  : Lemma (vec128_as_i16x8 (e_vaddq_s16 a b)
           == Spec.Utils.map2 ( +. ) (vec128_as_i16x8 a) (vec128_as_i16x8 b))
          [SMTPat (vec128_as_i16x8 (e_vaddq_s16 a b))] =
  NV.lemma_vaddq_s16 a b;
  Seq.lemma_eq_intro (vec128_as_i16x8 (e_vaddq_s16 a b))
                     (Spec.Utils.map2 ( +. ) (vec128_as_i16x8 a) (vec128_as_i16x8 b))
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vsubq_s16 (a b: t_e_int16x8_t)
  : Lemma (vec128_as_i16x8 (e_vsubq_s16 a b)
           == Spec.Utils.map2 ( -. ) (vec128_as_i16x8 a) (vec128_as_i16x8 b))
          [SMTPat (vec128_as_i16x8 (e_vsubq_s16 a b))] =
  NV.lemma_vsubq_s16 a b;
  Seq.lemma_eq_intro (vec128_as_i16x8 (e_vsubq_s16 a b))
                     (Spec.Utils.map2 ( -. ) (vec128_as_i16x8 a) (vec128_as_i16x8 b))
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vmulq_s16 (a b: t_e_int16x8_t)
  : Lemma (vec128_as_i16x8 (e_vmulq_s16 a b)
           == Spec.Utils.map2 mul_mod (vec128_as_i16x8 a) (vec128_as_i16x8 b))
          [SMTPat (vec128_as_i16x8 (e_vmulq_s16 a b))] =
  NV.lemma_vmulq_s16 a b;
  Seq.lemma_eq_intro (vec128_as_i16x8 (e_vmulq_s16 a b))
                     (Spec.Utils.map2 mul_mod (vec128_as_i16x8 a) (vec128_as_i16x8 b))
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vmulq_n_s16 (v: t_e_int16x8_t) (c: i16)
  : Lemma (vec128_as_i16x8 (e_vmulq_n_s16 v c)
           == Seq.init 8 (fun i -> Seq.index (vec128_as_i16x8 v) i *. c))
          [SMTPat (vec128_as_i16x8 (e_vmulq_n_s16 v c))] =
  NV.lemma_vmulq_n_s16 v c;
  Seq.lemma_eq_intro (vec128_as_i16x8 (e_vmulq_n_s16 v c))
                     (Seq.init 8 (fun i -> Seq.index (vec128_as_i16x8 v) i *. c))
#pop-options

(* ── i16x8 transpose op-facts (mirror pattern; used by the NEON NTT) ────────── *)
(* ArmIV.vtrn1q_s16 = from_fn (if i even then a[i] else b[i-1]) (interleave lows);
   vtrn2q_s16 = from_fn (if i even then a[i+1] else b[i]) (interleave highs). *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vtrn1q_s16 (a b: t_e_int16x8_t)
  : Lemma (vec128_as_i16x8 (e_vtrn1q_s16 a b)
           == Seq.init 8 (fun i -> if i % 2 = 0 then Seq.index (vec128_as_i16x8 a) i
                                              else Seq.index (vec128_as_i16x8 b) (i - 1)))
          [SMTPat (vec128_as_i16x8 (e_vtrn1q_s16 a b))] =
  NV.lemma_vtrn1q_s16 a b;
  Seq.lemma_eq_intro (vec128_as_i16x8 (e_vtrn1q_s16 a b))
                     (Seq.init 8 (fun i -> if i % 2 = 0 then Seq.index (vec128_as_i16x8 a) i
                                                    else Seq.index (vec128_as_i16x8 b) (i - 1)))
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vtrn2q_s16 (a b: t_e_int16x8_t)
  : Lemma (vec128_as_i16x8 (e_vtrn2q_s16 a b)
           == Seq.init 8 (fun i -> if i % 2 = 0 then Seq.index (vec128_as_i16x8 a) (i + 1)
                                              else Seq.index (vec128_as_i16x8 b) i))
          [SMTPat (vec128_as_i16x8 (e_vtrn2q_s16 a b))] =
  NV.lemma_vtrn2q_s16 a b;
  Seq.lemma_eq_intro (vec128_as_i16x8 (e_vtrn2q_s16 a b))
                     (Seq.init 8 (fun i -> if i % 2 = 0 then Seq.index (vec128_as_i16x8 a) (i + 1)
                                                    else Seq.index (vec128_as_i16x8 b) i))
#pop-options
