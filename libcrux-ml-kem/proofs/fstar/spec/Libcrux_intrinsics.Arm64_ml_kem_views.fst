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
   VALIDATED i16x8 "per-lane-codec backbone" (8 op-facts): the structural i16x8
   lane view + arithmetic (`vadd/vsub/vmul/vmul_n_s16`), transpose
   (`vtrn1q/vtrn2q_s16`), broadcast (`vdupq_n_s16`) and right-shift
   (`vshrq_n_s16`), which prove directly from the `Neon_views` codec op-lemmas
   (`ArmIV.OP` is a per-lane FunArray op, so `Seq.init`/`map2 f (view a) (view b)`
   matches by `Seq.lemma_eq_intro`).  All gated green via `make check/...` at
   rlimit < 2.4.

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

(* ── i16x8 broadcast + right-shift op-facts (mirror pattern) ────────────────── *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vdupq_n_s16 (c: i16)
  : Lemma (vec128_as_i16x8 (e_vdupq_n_s16 c) == Seq.create 8 c)
          [SMTPat (vec128_as_i16x8 (e_vdupq_n_s16 c))] =
  NV.lemma_vdupq_n_s16 c;
  Seq.lemma_eq_intro (vec128_as_i16x8 (e_vdupq_n_s16 c)) (Seq.create 8 c)
#pop-options

(* Full ArmIV mirror (all shift ranges); consumers with 0<=SHIFT<16 reduce to
   the `>>! SHIFT` branch. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vshrq_n_s16 (v_SHIFT_BY: i32) (v: t_e_int16x8_t)
  : Lemma (vec128_as_i16x8 (e_vshrq_n_s16 v_SHIFT_BY v)
           == Seq.init 8 (fun i ->
                let x = Seq.index (vec128_as_i16x8 v) i in
                if v_SHIFT_BY >=. mk_i32 16 then (if x <. mk_i16 0 then mk_i16 (-1) else mk_i16 0)
                else if v_SHIFT_BY <=. mk_i32 0 then x
                else x >>! v_SHIFT_BY))
          [SMTPat (vec128_as_i16x8 (e_vshrq_n_s16 v_SHIFT_BY v))] =
  NV.lemma_vshrq_n_s16 v_SHIFT_BY v;
  Seq.lemma_eq_intro (vec128_as_i16x8 (e_vshrq_n_s16 v_SHIFT_BY v))
                     (Seq.init 8 (fun i ->
                        let x = Seq.index (vec128_as_i16x8 v) i in
                        if v_SHIFT_BY >=. mk_i32 16 then (if x <. mk_i16 0 then mk_i16 (-1) else mk_i16 0)
                        else if v_SHIFT_BY <=. mk_i32 0 then x
                        else x >>! v_SHIFT_BY))
#pop-options

(* ============================================================================
   TIER A — other-width lane views + Shape-A per-lane-codec op-facts.

   Same validated recipe as the i16x8 backbone: the real `Arm64.e_vOP`
   delegates to `Neon.OP` (transparent), the canonical `NV.lemma_vOP` gives the
   VIEW-level `to_WxL (Neon.OP ...) == ArmIV.OP (to_WxL a) ...`, `ArmIV.OP` is a
   per-lane FunArray op, so `Seq.lemma_eq_intro` closes against `Spec.Utils.map2`
   / `Seq.init` / `Seq.create`.  Signed views read `Canon.to_iWxL`; unsigned read
   `NV.to_uWxL` (the exact codec each `NV.lemma_*` is stated over).
   ========================================================================== *)

(* ── i32x4 lane view ──────────────────────────────────────────────────────── *)
[@@ "opaque_to_smt"]
let vec128_as_i32x4 (x: t_e_int32x4_t) : t_Array i32 (sz 4) =
  Seq.init 4 (fun i -> Funarr.impl_5__get (mk_u64 4) #i32 (Canon.to_i32x4 x) (mk_u64 i))
let get_lane_i32x4 (v: t_e_int32x4_t) (i: nat{i < 4}) : i32 = Seq.index (vec128_as_i32x4 v) i

let vec128_index_i32x4 (x: t_e_int32x4_t) (i: nat{i < 4})
  : Lemma (Seq.index (vec128_as_i32x4 x) i
           == Funarr.impl_5__get (mk_u64 4) #i32 (Canon.to_i32x4 x) (mk_u64 i))
          [SMTPat (Seq.index (vec128_as_i32x4 x) i)]
  = reveal_opaque (`%vec128_as_i32x4) vec128_as_i32x4

let vec128_as_i32x4_len (x: t_e_int32x4_t)
  : Lemma (Seq.length (vec128_as_i32x4 x) == 4)
          [SMTPat (Seq.length (vec128_as_i32x4 x))]
  = ()

let vec128_as_i32x4_slice_ok (x: t_e_int32x4_t)
  : Lemma (Seq.length (vec128_as_i32x4 x) <= Rust_primitives.Integers.max_usize)
          [SMTPat (vec128_as_i32x4 x)]
  = assert_norm (4 <= Rust_primitives.Integers.max_usize)

(* ── i64x2 lane view ──────────────────────────────────────────────────────── *)
[@@ "opaque_to_smt"]
let vec128_as_i64x2 (x: t_e_int64x2_t) : t_Array i64 (sz 2) =
  Seq.init 2 (fun i -> Funarr.impl_5__get (mk_u64 2) #i64 (Canon.to_i64x2 x) (mk_u64 i))
let get_lane_i64x2 (v: t_e_int64x2_t) (i: nat{i < 2}) : i64 = Seq.index (vec128_as_i64x2 v) i

let vec128_index_i64x2 (x: t_e_int64x2_t) (i: nat{i < 2})
  : Lemma (Seq.index (vec128_as_i64x2 x) i
           == Funarr.impl_5__get (mk_u64 2) #i64 (Canon.to_i64x2 x) (mk_u64 i))
          [SMTPat (Seq.index (vec128_as_i64x2 x) i)]
  = reveal_opaque (`%vec128_as_i64x2) vec128_as_i64x2

let vec128_as_i64x2_len (x: t_e_int64x2_t)
  : Lemma (Seq.length (vec128_as_i64x2 x) == 2)
          [SMTPat (Seq.length (vec128_as_i64x2 x))]
  = ()

let vec128_as_i64x2_slice_ok (x: t_e_int64x2_t)
  : Lemma (Seq.length (vec128_as_i64x2 x) <= Rust_primitives.Integers.max_usize)
          [SMTPat (vec128_as_i64x2 x)]
  = assert_norm (2 <= Rust_primitives.Integers.max_usize)

(* ── u32x4 lane view ──────────────────────────────────────────────────────── *)
[@@ "opaque_to_smt"]
let vec128_as_u32x4 (x: t_e_uint32x4_t) : t_Array u32 (sz 4) =
  Seq.init 4 (fun i -> Funarr.impl_5__get (mk_u64 4) #u32 (NV.to_u32x4 x) (mk_u64 i))
let get_lane_u32x4 (v: t_e_uint32x4_t) (i: nat{i < 4}) : u32 = Seq.index (vec128_as_u32x4 v) i

let vec128_index_u32x4 (x: t_e_uint32x4_t) (i: nat{i < 4})
  : Lemma (Seq.index (vec128_as_u32x4 x) i
           == Funarr.impl_5__get (mk_u64 4) #u32 (NV.to_u32x4 x) (mk_u64 i))
          [SMTPat (Seq.index (vec128_as_u32x4 x) i)]
  = reveal_opaque (`%vec128_as_u32x4) vec128_as_u32x4

let vec128_as_u32x4_len (x: t_e_uint32x4_t)
  : Lemma (Seq.length (vec128_as_u32x4 x) == 4)
          [SMTPat (Seq.length (vec128_as_u32x4 x))]
  = ()

let vec128_as_u32x4_slice_ok (x: t_e_uint32x4_t)
  : Lemma (Seq.length (vec128_as_u32x4 x) <= Rust_primitives.Integers.max_usize)
          [SMTPat (vec128_as_u32x4 x)]
  = assert_norm (4 <= Rust_primitives.Integers.max_usize)

(* ── u16x8 lane view ──────────────────────────────────────────────────────── *)
[@@ "opaque_to_smt"]
let vec128_as_u16x8 (x: t_e_uint16x8_t) : t_Array u16 (sz 8) =
  Seq.init 8 (fun i -> Funarr.impl_5__get (mk_u64 8) #u16 (NV.to_u16x8 x) (mk_u64 i))
let get_lane_u16x8 (v: t_e_uint16x8_t) (i: nat{i < 8}) : u16 = Seq.index (vec128_as_u16x8 v) i

let vec128_index_u16x8 (x: t_e_uint16x8_t) (i: nat{i < 8})
  : Lemma (Seq.index (vec128_as_u16x8 x) i
           == Funarr.impl_5__get (mk_u64 8) #u16 (NV.to_u16x8 x) (mk_u64 i))
          [SMTPat (Seq.index (vec128_as_u16x8 x) i)]
  = reveal_opaque (`%vec128_as_u16x8) vec128_as_u16x8

let vec128_as_u16x8_len (x: t_e_uint16x8_t)
  : Lemma (Seq.length (vec128_as_u16x8 x) == 8)
          [SMTPat (Seq.length (vec128_as_u16x8 x))]
  = ()

let vec128_as_u16x8_slice_ok (x: t_e_uint16x8_t)
  : Lemma (Seq.length (vec128_as_u16x8 x) <= Rust_primitives.Integers.max_usize)
          [SMTPat (vec128_as_u16x8 x)]
  = assert_norm (8 <= Rust_primitives.Integers.max_usize)

(* ── i32x4 transpose (used by the NEON NTT butterfly interleave) ───────────── *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vtrn1q_s32 (a b: t_e_int32x4_t)
  : Lemma (vec128_as_i32x4 (e_vtrn1q_s32 a b)
           == Seq.init 4 (fun i -> if i % 2 = 0 then Seq.index (vec128_as_i32x4 a) i
                                              else Seq.index (vec128_as_i32x4 b) (i - 1)))
          [SMTPat (vec128_as_i32x4 (e_vtrn1q_s32 a b))] =
  NV.lemma_vtrn1q_s32 a b;
  Seq.lemma_eq_intro (vec128_as_i32x4 (e_vtrn1q_s32 a b))
                     (Seq.init 4 (fun i -> if i % 2 = 0 then Seq.index (vec128_as_i32x4 a) i
                                                    else Seq.index (vec128_as_i32x4 b) (i - 1)))
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vtrn2q_s32 (a b: t_e_int32x4_t)
  : Lemma (vec128_as_i32x4 (e_vtrn2q_s32 a b)
           == Seq.init 4 (fun i -> if i % 2 = 0 then Seq.index (vec128_as_i32x4 a) (i + 1)
                                              else Seq.index (vec128_as_i32x4 b) i))
          [SMTPat (vec128_as_i32x4 (e_vtrn2q_s32 a b))] =
  NV.lemma_vtrn2q_s32 a b;
  Seq.lemma_eq_intro (vec128_as_i32x4 (e_vtrn2q_s32 a b))
                     (Seq.init 4 (fun i -> if i % 2 = 0 then Seq.index (vec128_as_i32x4 a) (i + 1)
                                                    else Seq.index (vec128_as_i32x4 b) i))
#pop-options

(* ── i64x2 transpose ──────────────────────────────────────────────────────── *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vtrn1q_s64 (a b: t_e_int64x2_t)
  : Lemma (vec128_as_i64x2 (e_vtrn1q_s64 a b)
           == Seq.init 2 (fun i -> if i % 2 = 0 then Seq.index (vec128_as_i64x2 a) i
                                              else Seq.index (vec128_as_i64x2 b) (i - 1)))
          [SMTPat (vec128_as_i64x2 (e_vtrn1q_s64 a b))] =
  NV.lemma_vtrn1q_s64 a b;
  Seq.lemma_eq_intro (vec128_as_i64x2 (e_vtrn1q_s64 a b))
                     (Seq.init 2 (fun i -> if i % 2 = 0 then Seq.index (vec128_as_i64x2 a) i
                                                    else Seq.index (vec128_as_i64x2 b) (i - 1)))
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vtrn2q_s64 (a b: t_e_int64x2_t)
  : Lemma (vec128_as_i64x2 (e_vtrn2q_s64 a b)
           == Seq.init 2 (fun i -> if i % 2 = 0 then Seq.index (vec128_as_i64x2 a) (i + 1)
                                              else Seq.index (vec128_as_i64x2 b) i))
          [SMTPat (vec128_as_i64x2 (e_vtrn2q_s64 a b))] =
  NV.lemma_vtrn2q_s64 a b;
  Seq.lemma_eq_intro (vec128_as_i64x2 (e_vtrn2q_s64 a b))
                     (Seq.init 2 (fun i -> if i % 2 = 0 then Seq.index (vec128_as_i64x2 a) (i + 1)
                                                    else Seq.index (vec128_as_i64x2 b) i))
#pop-options

(* ── u32x4 arithmetic / shifts / broadcast ────────────────────────────────── *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vaddq_u32 (a b: t_e_uint32x4_t)
  : Lemma (vec128_as_u32x4 (e_vaddq_u32 a b)
           == Spec.Utils.map2 ( +. ) (vec128_as_u32x4 a) (vec128_as_u32x4 b))
          [SMTPat (vec128_as_u32x4 (e_vaddq_u32 a b))] =
  NV.lemma_vaddq_u32 a b;
  Seq.lemma_eq_intro (vec128_as_u32x4 (e_vaddq_u32 a b))
                     (Spec.Utils.map2 ( +. ) (vec128_as_u32x4 a) (vec128_as_u32x4 b))
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vmulq_n_u32 (a: t_e_uint32x4_t) (c: u32)
  : Lemma (vec128_as_u32x4 (e_vmulq_n_u32 a c)
           == Seq.init 4 (fun i -> Seq.index (vec128_as_u32x4 a) i *. c))
          [SMTPat (vec128_as_u32x4 (e_vmulq_n_u32 a c))] =
  NV.lemma_vmulq_n_u32 a c;
  Seq.lemma_eq_intro (vec128_as_u32x4 (e_vmulq_n_u32 a c))
                     (Seq.init 4 (fun i -> Seq.index (vec128_as_u32x4 a) i *. c))
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vdupq_n_u32 (c: u32)
  : Lemma (vec128_as_u32x4 (e_vdupq_n_u32 c) == Seq.create 4 c)
          [SMTPat (vec128_as_u32x4 (e_vdupq_n_u32 c))] =
  NV.lemma_vdupq_n_u32 c;
  Seq.lemma_eq_intro (vec128_as_u32x4 (e_vdupq_n_u32 c)) (Seq.create 4 c)
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vshrq_n_u32 (v_N: i32) (a: t_e_uint32x4_t)
  : Lemma (vec128_as_u32x4 (e_vshrq_n_u32 v_N a)
           == Seq.init 4 (fun i ->
                let x = Seq.index (vec128_as_u32x4 a) i in
                if v_N >=. mk_i32 32 then mk_u32 0
                else if v_N <=. mk_i32 0 then x
                else x >>! (cast v_N <: u32)))
          [SMTPat (vec128_as_u32x4 (e_vshrq_n_u32 v_N a))] =
  NV.lemma_vshrq_n_u32 v_N a;
  Seq.lemma_eq_intro (vec128_as_u32x4 (e_vshrq_n_u32 v_N a))
                     (Seq.init 4 (fun i ->
                        let x = Seq.index (vec128_as_u32x4 a) i in
                        if v_N >=. mk_i32 32 then mk_u32 0
                        else if v_N <=. mk_i32 0 then x
                        else x >>! (cast v_N <: u32)))
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vshlq_n_u32 (v_SHIFT_BY: i32) (a: t_e_uint32x4_t)
  : Lemma (vec128_as_u32x4 (e_vshlq_n_u32 v_SHIFT_BY a)
           == Seq.init 4 (fun i ->
                let x = Seq.index (vec128_as_u32x4 a) i in
                if v_SHIFT_BY >=. mk_i32 32 || v_SHIFT_BY <. mk_i32 0 then mk_u32 0
                else x <<! (cast v_SHIFT_BY <: u32)))
          [SMTPat (vec128_as_u32x4 (e_vshlq_n_u32 v_SHIFT_BY a))] =
  NV.lemma_vshlq_n_u32 v_SHIFT_BY a;
  Seq.lemma_eq_intro (vec128_as_u32x4 (e_vshlq_n_u32 v_SHIFT_BY a))
                     (Seq.init 4 (fun i ->
                        let x = Seq.index (vec128_as_u32x4 a) i in
                        if v_SHIFT_BY >=. mk_i32 32 || v_SHIFT_BY <. mk_i32 0 then mk_u32 0
                        else x <<! (cast v_SHIFT_BY <: u32)))
#pop-options

(* ── u16x8 arithmetic / shift / broadcast ─────────────────────────────────── *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vmulq_n_u16 (a: t_e_uint16x8_t) (c: u16)
  : Lemma (vec128_as_u16x8 (e_vmulq_n_u16 a c)
           == Seq.init 8 (fun i -> Seq.index (vec128_as_u16x8 a) i *. c))
          [SMTPat (vec128_as_u16x8 (e_vmulq_n_u16 a c))] =
  NV.lemma_vmulq_n_u16 a c;
  Seq.lemma_eq_intro (vec128_as_u16x8 (e_vmulq_n_u16 a c))
                     (Seq.init 8 (fun i -> Seq.index (vec128_as_u16x8 a) i *. c))
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vdupq_n_u16 (c: u16)
  : Lemma (vec128_as_u16x8 (e_vdupq_n_u16 c) == Seq.create 8 c)
          [SMTPat (vec128_as_u16x8 (e_vdupq_n_u16 c))] =
  NV.lemma_vdupq_n_u16 c;
  Seq.lemma_eq_intro (vec128_as_u16x8 (e_vdupq_n_u16 c)) (Seq.create 8 c)
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vshrq_n_u16 (v_SHIFT_BY: i32) (v: t_e_uint16x8_t)
  : Lemma (vec128_as_u16x8 (e_vshrq_n_u16 v_SHIFT_BY v)
           == Seq.init 8 (fun i ->
                let x = Seq.index (vec128_as_u16x8 v) i in
                if v_SHIFT_BY >=. mk_i32 16 then mk_u16 0
                else if v_SHIFT_BY <=. mk_i32 0 then x
                else x >>! v_SHIFT_BY))
          [SMTPat (vec128_as_u16x8 (e_vshrq_n_u16 v_SHIFT_BY v))] =
  NV.lemma_vshrq_n_u16 v_SHIFT_BY v;
  Seq.lemma_eq_intro (vec128_as_u16x8 (e_vshrq_n_u16 v_SHIFT_BY v))
                     (Seq.init 8 (fun i ->
                        let x = Seq.index (vec128_as_u16x8 v) i in
                        if v_SHIFT_BY >=. mk_i32 16 then mk_u16 0
                        else if v_SHIFT_BY <=. mk_i32 0 then x
                        else x >>! v_SHIFT_BY))
#pop-options

(* ── ARM variable-shift helper lets (copied verbatim from the pcm
      `Arm64_extract.fsti` — referenced by the vshlq_s16/u16 op-facts and by
      consumer proofs). ───────────────────────────────────────────────────── *)
let arm_sshl_i16 (a b: i16) : i16 =
  let s = v (b %! mk_i16 256) in
  if s < 128 then (if s < 16 then a <<! mk_i32 s else mk_i16 0)
  else (let r = 256 - s in
        if r < 16 then a >>! mk_i32 r
        else (if a <. mk_i16 0 then mk_i16 (-1) else mk_i16 0))

let arm_ushl_u16 (a: u16) (b: i16) : u16 =
  let s = v (b %! mk_i16 256) in
  if s < 128 then (if s < 16 then a <<! mk_i32 s else mk_u16 0)
  else (let r = 256 - s in
        if r < 16 then a >>! mk_i32 r else mk_u16 0)

(* ── i16x8 saturating doubling multiply-high (vqdmulh) ────────────────────── *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vqdmulhq_n_s16 (k: t_e_int16x8_t) (b: i16)
  : Lemma (vec128_as_i16x8 (e_vqdmulhq_n_s16 k b)
           == Seq.init 8 (fun i ->
                let prod = ((cast (Seq.index (vec128_as_i16x8 k) i) <: i32) *. (cast b <: i32)) >>! (mk_i32 15) in
                if prod >. mk_i32 32767 then mk_i16 32767
                else if prod <. mk_i32 (- 32768) then mk_i16 (- 32768) else (cast prod <: i16)))
          [SMTPat (vec128_as_i16x8 (e_vqdmulhq_n_s16 k b))] =
  NV.lemma_vqdmulhq_n_s16 k b;
  Seq.lemma_eq_intro (vec128_as_i16x8 (e_vqdmulhq_n_s16 k b))
                     (Seq.init 8 (fun i ->
                        let prod = ((cast (Seq.index (vec128_as_i16x8 k) i) <: i32) *. (cast b <: i32)) >>! (mk_i32 15) in
                        if prod >. mk_i32 32767 then mk_i16 32767
                        else if prod <. mk_i32 (- 32768) then mk_i16 (- 32768) else (cast prod <: i16)))
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vqdmulhq_s16 (a c: t_e_int16x8_t)
  : Lemma (vec128_as_i16x8 (e_vqdmulhq_s16 a c)
           == Seq.init 8 (fun i ->
                let prod = ((cast (Seq.index (vec128_as_i16x8 a) i) <: i32)
                            *. (cast (Seq.index (vec128_as_i16x8 c) i) <: i32)) >>! (mk_i32 15) in
                if prod >. mk_i32 32767 then mk_i16 32767
                else if prod <. mk_i32 (- 32768) then mk_i16 (- 32768) else (cast prod <: i16)))
          [SMTPat (vec128_as_i16x8 (e_vqdmulhq_s16 a c))] =
  NV.lemma_vqdmulhq_s16 a c;
  Seq.lemma_eq_intro (vec128_as_i16x8 (e_vqdmulhq_s16 a c))
                     (Seq.init 8 (fun i ->
                        let prod = ((cast (Seq.index (vec128_as_i16x8 a) i) <: i32)
                                    *. (cast (Seq.index (vec128_as_i16x8 c) i) <: i32)) >>! (mk_i32 15) in
                        if prod >. mk_i32 32767 then mk_i16 32767
                        else if prod <. mk_i32 (- 32768) then mk_i16 (- 32768) else (cast prod <: i16)))
#pop-options

(* ── i16x8 comparison -> u16x8 mask ───────────────────────────────────────── *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vcgeq_s16 (v c: t_e_int16x8_t)
  : Lemma (vec128_as_u16x8 (e_vcgeq_s16 v c)
           == Seq.init 8 (fun i ->
                if Seq.index (vec128_as_i16x8 v) i >=. Seq.index (vec128_as_i16x8 c) i
                then mk_u16 0xFFFF else mk_u16 0))
          [SMTPat (vec128_as_u16x8 (e_vcgeq_s16 v c))] =
  NV.lemma_vcgeq_s16 v c;
  Seq.lemma_eq_intro (vec128_as_u16x8 (e_vcgeq_s16 v c))
                     (Seq.init 8 (fun i ->
                        if Seq.index (vec128_as_i16x8 v) i >=. Seq.index (vec128_as_i16x8 c) i
                        then mk_u16 0xFFFF else mk_u16 0))
#pop-options

(* vshlq_s16 / vshlq_u16 op-facts deferred: `arm_sshl_i16` / `arm_ushl_u16`
   (pcm's `v (b %! 256)` split-at-128 encoding) are only PROVABLY equal to the
   core-models `ArmIV.vshlq_s16` lane body (sign-extended low-byte + data-
   dependent shift) via a dedicated per-lane byte/shift bridge lemma; see the
   `lemma_arm_sshl_eq` work below. *)

(* ── 64-bit half-vector lane views (i16x4 / u16x4) ────────────────────────── *)
[@@ "opaque_to_smt"]
let vec64_as_i16x4 (x: t_e_int16x4_t) : t_Array i16 (sz 4) =
  Seq.init 4 (fun i -> Funarr.impl_5__get (mk_u64 4) #i16 (NV.to_i16x4 x) (mk_u64 i))
let get_lane_i16x4 (v: t_e_int16x4_t) (i: nat{i < 4}) : i16 = Seq.index (vec64_as_i16x4 v) i

let vec64_index_i16x4 (x: t_e_int16x4_t) (i: nat{i < 4})
  : Lemma (Seq.index (vec64_as_i16x4 x) i
           == Funarr.impl_5__get (mk_u64 4) #i16 (NV.to_i16x4 x) (mk_u64 i))
          [SMTPat (Seq.index (vec64_as_i16x4 x) i)]
  = reveal_opaque (`%vec64_as_i16x4) vec64_as_i16x4

let vec64_as_i16x4_len (x: t_e_int16x4_t)
  : Lemma (Seq.length (vec64_as_i16x4 x) == 4)
          [SMTPat (Seq.length (vec64_as_i16x4 x))]
  = ()

let vec64_as_i16x4_slice_ok (x: t_e_int16x4_t)
  : Lemma (Seq.length (vec64_as_i16x4 x) <= Rust_primitives.Integers.max_usize)
          [SMTPat (vec64_as_i16x4 x)]
  = assert_norm (4 <= Rust_primitives.Integers.max_usize)

[@@ "opaque_to_smt"]
let vec64_as_u16x4 (x: t_e_uint16x4_t) : t_Array u16 (sz 4) =
  Seq.init 4 (fun i -> Funarr.impl_5__get (mk_u64 4) #u16 (NV.to_u16x4 x) (mk_u64 i))
let get_lane_u16x4 (v: t_e_uint16x4_t) (i: nat{i < 4}) : u16 = Seq.index (vec64_as_u16x4 v) i

let vec64_index_u16x4 (x: t_e_uint16x4_t) (i: nat{i < 4})
  : Lemma (Seq.index (vec64_as_u16x4 x) i
           == Funarr.impl_5__get (mk_u64 4) #u16 (NV.to_u16x4 x) (mk_u64 i))
          [SMTPat (Seq.index (vec64_as_u16x4 x) i)]
  = reveal_opaque (`%vec64_as_u16x4) vec64_as_u16x4

let vec64_as_u16x4_len (x: t_e_uint16x4_t)
  : Lemma (Seq.length (vec64_as_u16x4 x) == 4)
          [SMTPat (Seq.length (vec64_as_u16x4 x))]
  = ()

let vec64_as_u16x4_slice_ok (x: t_e_uint16x4_t)
  : Lemma (Seq.length (vec64_as_u16x4 x) <= Rust_primitives.Integers.max_usize)
          [SMTPat (vec64_as_u16x4 x)]
  = assert_norm (4 <= Rust_primitives.Integers.max_usize)

(* ── get low / high half (128 -> 64) ──────────────────────────────────────── *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vget_low_s16 (a: t_e_int16x8_t)
  : Lemma (vec64_as_i16x4 (e_vget_low_s16 a)
           == Seq.init 4 (fun i -> Seq.index (vec128_as_i16x8 a) i))
          [SMTPat (vec64_as_i16x4 (e_vget_low_s16 a))] =
  NV.lemma_vget_low_s16 a;
  Seq.lemma_eq_intro (vec64_as_i16x4 (e_vget_low_s16 a))
                     (Seq.init 4 (fun i -> Seq.index (vec128_as_i16x8 a) i))
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vget_low_u16 (a: t_e_uint16x8_t)
  : Lemma (vec64_as_u16x4 (e_vget_low_u16 a)
           == Seq.init 4 (fun i -> Seq.index (vec128_as_u16x8 a) i))
          [SMTPat (vec64_as_u16x4 (e_vget_low_u16 a))] =
  NV.lemma_vget_low_u16 a;
  Seq.lemma_eq_intro (vec64_as_u16x4 (e_vget_low_u16 a))
                     (Seq.init 4 (fun i -> Seq.index (vec128_as_u16x8 a) i))
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vget_high_u16 (a: t_e_uint16x8_t)
  : Lemma (vec64_as_u16x4 (e_vget_high_u16 a)
           == Seq.init 4 (fun i -> Seq.index (vec128_as_u16x8 a) (i + 4)))
          [SMTPat (vec64_as_u16x4 (e_vget_high_u16 a))] =
  NV.lemma_vget_high_u16 a;
  Seq.lemma_eq_intro (vec64_as_u16x4 (e_vget_high_u16 a))
                     (Seq.init 4 (fun i -> Seq.index (vec128_as_u16x8 a) (i + 4)))
#pop-options

(* ── widening multiply (i16x4 / high halves -> i32x4) ─────────────────────── *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vmull_s16 (a b: t_e_int16x4_t)
  : Lemma (vec128_as_i32x4 (e_vmull_s16 a b)
           == Seq.init 4 (fun i -> (cast (Seq.index (vec64_as_i16x4 a) i) <: i32)
                                *. (cast (Seq.index (vec64_as_i16x4 b) i) <: i32)))
          [SMTPat (vec128_as_i32x4 (e_vmull_s16 a b))] =
  NV.lemma_vmull_s16 a b;
  Seq.lemma_eq_intro (vec128_as_i32x4 (e_vmull_s16 a b))
                     (Seq.init 4 (fun i -> (cast (Seq.index (vec64_as_i16x4 a) i) <: i32)
                                        *. (cast (Seq.index (vec64_as_i16x4 b) i) <: i32)))
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_e_vmull_high_s16 (a b: t_e_int16x8_t)
  : Lemma (vec128_as_i32x4 (e_vmull_high_s16 a b)
           == Seq.init 4 (fun i -> (cast (Seq.index (vec128_as_i16x8 a) (i + 4)) <: i32)
                                *. (cast (Seq.index (vec128_as_i16x8 b) (i + 4)) <: i32)))
          [SMTPat (vec128_as_i32x4 (e_vmull_high_s16 a b))] =
  NV.lemma_vmull_high_s16 a b;
  Seq.lemma_eq_intro (vec128_as_i32x4 (e_vmull_high_s16 a b))
                     (Seq.init 4 (fun i -> (cast (Seq.index (vec128_as_i16x8 a) (i + 4)) <: i32)
                                        *. (cast (Seq.index (vec128_as_i16x8 b) (i + 4)) <: i32)))
#pop-options

(* vaddvq_s16 / vaddv_u16 horizontal-reduction op-facts deferred: the core-models
   `ArmIV.vaddvq_s16` is a LEFT fold_range (wrapping_add accumulate), while the
   pcm/consumer form is the BALANCED sum tree `((a0+a1)+(a2+a3))+((a4+a5)+(a6+a7))`.
   Equal only via AC-normalization of i16 add_mod + fold unfolding — a dedicated
   reduction bridge lemma. *)
