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
module IVi    = Libcrux_core_models.Abstractions.Bitvec.Int_vec_interp
module Int    = Rust_primitives.Integers
module Bit    = Libcrux_core_models.Abstractions.Bit

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

(* ── u8x16 lane view ──────────────────────────────────────────────────────── *)
[@@ "opaque_to_smt"]
let vec128_as_u8x16 (x: t_e_uint8x16_t) : t_Array u8 (sz 16) =
  Seq.init 16 (fun i -> Funarr.impl_5__get (mk_u64 16) #u8 (NV.to_u8x16 x) (mk_u64 i))
let get_lane_u8x16 (v: t_e_uint8x16_t) (i: nat{i < 16}) : u8 = Seq.index (vec128_as_u8x16 v) i

let vec128_index_u8x16 (x: t_e_uint8x16_t) (i: nat{i < 16})
  : Lemma (Seq.index (vec128_as_u8x16 x) i
           == Funarr.impl_5__get (mk_u64 16) #u8 (NV.to_u8x16 x) (mk_u64 i))
          [SMTPat (Seq.index (vec128_as_u8x16 x) i)]
  = reveal_opaque (`%vec128_as_u8x16) vec128_as_u8x16

let vec128_as_u8x16_len (x: t_e_uint8x16_t)
  : Lemma (Seq.length (vec128_as_u8x16 x) == 16)
          [SMTPat (Seq.length (vec128_as_u8x16 x))]
  = ()

let vec128_as_u8x16_slice_ok (x: t_e_uint8x16_t)
  : Lemma (Seq.length (vec128_as_u8x16 x) <= Rust_primitives.Integers.max_usize)
          [SMTPat (vec128_as_u8x16 x)]
  = assert_norm (16 <= Rust_primitives.Integers.max_usize)

(* ── table lookup (vqtbl1q_u8): data-dependent per-byte select ────────────── *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 200"
let lemma_e_vqtbl1q_u8 (t idx: t_e_uint8x16_t)
  : Lemma (vec128_as_u8x16 (e_vqtbl1q_u8 t idx)
           == Seq.init 16 (fun i ->
                let ix = v (Seq.index (vec128_as_u8x16 idx) i) in
                if ix < 16 then Seq.index (vec128_as_u8x16 t) ix else mk_u8 0))
          [SMTPat (vec128_as_u8x16 (e_vqtbl1q_u8 t idx))] =
  NV.lemma_vqtbl1q_u8 t idx;
  Seq.lemma_eq_intro (vec128_as_u8x16 (e_vqtbl1q_u8 t idx))
                     (Seq.init 16 (fun i ->
                        let ix = v (Seq.index (vec128_as_u8x16 idx) i) in
                        if ix < 16 then Seq.index (vec128_as_u8x16 t) ix else mk_u8 0))
#pop-options

(* ============================================================================
   TIER C/D (part 1) — reinterpret BIT-IDENTITY.  Every NEON reinterpret is a
   pure bit relabel: the real op delegates to `Neon.OP`, `NV.lemma_vreinterpretq_*`
   gives `Neon.OP a == ArmIV.OP a`, and `ArmIV.vreinterpretq_* a == a`
   (definitional `let OP a = a`).  So `result == a` for every reinterpret.  The
   per-lane cross-/same-width repack (i16x2_as_i32 / i32_lo16_as_i16 / cast_mod /
   ...) is a SEPARATE codec fact added on top (Tier C/D part 2) — this identity
   is what lets a consumer carry a value across a reinterpret unchanged.
   ========================================================================== *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let lemma_e_vreinterpretq_s16_u16 (m0: t_e_uint16x8_t)
  : Lemma (e_vreinterpretq_s16_u16 m0 == m0) [SMTPat (e_vreinterpretq_s16_u16 m0)] =
  NV.lemma_vreinterpretq_s16_u16 m0
let lemma_e_vreinterpretq_u16_s16 (m0: t_e_int16x8_t)
  : Lemma (e_vreinterpretq_u16_s16 m0 == m0) [SMTPat (e_vreinterpretq_u16_s16 m0)] =
  NV.lemma_vreinterpretq_u16_s16 m0
let lemma_e_vreinterpretq_s32_u32 (a: t_e_uint32x4_t)
  : Lemma (e_vreinterpretq_s32_u32 a == a) [SMTPat (e_vreinterpretq_s32_u32 a)] =
  NV.lemma_vreinterpretq_s32_u32 a
let lemma_e_vreinterpretq_u32_s32 (a: t_e_int32x4_t)
  : Lemma (e_vreinterpretq_u32_s32 a == a) [SMTPat (e_vreinterpretq_u32_s32 a)] =
  NV.lemma_vreinterpretq_u32_s32 a
let lemma_e_vreinterpretq_s16_s32 (a: t_e_int32x4_t)
  : Lemma (e_vreinterpretq_s16_s32 a == a) [SMTPat (e_vreinterpretq_s16_s32 a)] =
  NV.lemma_vreinterpretq_s16_s32 a
let lemma_e_vreinterpretq_s32_s16 (a: t_e_int16x8_t)
  : Lemma (e_vreinterpretq_s32_s16 a == a) [SMTPat (e_vreinterpretq_s32_s16 a)] =
  NV.lemma_vreinterpretq_s32_s16 a
let lemma_e_vreinterpretq_s16_s64 (a: t_e_int64x2_t)
  : Lemma (e_vreinterpretq_s16_s64 a == a) [SMTPat (e_vreinterpretq_s16_s64 a)] =
  NV.lemma_vreinterpretq_s16_s64 a
let lemma_e_vreinterpretq_s64_s16 (a: t_e_int16x8_t)
  : Lemma (e_vreinterpretq_s64_s16 a == a) [SMTPat (e_vreinterpretq_s64_s16 a)] =
  NV.lemma_vreinterpretq_s64_s16 a
let lemma_e_vreinterpretq_s64_s32 (a: t_e_int32x4_t)
  : Lemma (e_vreinterpretq_s64_s32 a == a) [SMTPat (e_vreinterpretq_s64_s32 a)] =
  NV.lemma_vreinterpretq_s64_s32 a
let lemma_e_vreinterpretq_u32_s16 (a: t_e_int16x8_t)
  : Lemma (e_vreinterpretq_u32_s16 a == a) [SMTPat (e_vreinterpretq_u32_s16 a)] =
  NV.lemma_vreinterpretq_u32_s16 a
let lemma_e_vreinterpretq_s16_u32 (a: t_e_uint32x4_t)
  : Lemma (e_vreinterpretq_s16_u32 a == a) [SMTPat (e_vreinterpretq_s16_u32 a)] =
  NV.lemma_vreinterpretq_s16_u32 a
let lemma_e_vreinterpretq_u8_s16 (a: t_e_int16x8_t)
  : Lemma (e_vreinterpretq_u8_s16 a == a) [SMTPat (e_vreinterpretq_u8_s16 a)] =
  NV.lemma_vreinterpretq_u8_s16 a
let lemma_e_vreinterpretq_s16_u8 (a: t_e_uint8x16_t)
  : Lemma (e_vreinterpretq_s16_u8 a == a) [SMTPat (e_vreinterpretq_s16_u8 a)] =
  NV.lemma_vreinterpretq_s16_u8 a
let lemma_e_vreinterpretq_u16_u8 (a: t_e_uint8x16_t)
  : Lemma (e_vreinterpretq_u16_u8 a == a) [SMTPat (e_vreinterpretq_u16_u8 a)] =
  NV.lemma_vreinterpretq_u16_u8 a
let lemma_e_vreinterpretq_u8_s64 (a: t_e_int64x2_t)
  : Lemma (e_vreinterpretq_u8_s64 a == a) [SMTPat (e_vreinterpretq_u8_s64 a)] =
  NV.lemma_vreinterpretq_u8_s64 a
#pop-options

(* ============================================================================
   TIER C (part 2) — codec-value foundation + the i32<->u32 signedness bridge.

   Width-128 analogs of `Intrinsics_views.lemma_to_i32_val` (the shared codec
   `to_iv` decodes lane k of a 128-bit reg as the two's-complement of the raw
   32-bit slice value).  Both the i32 and u32 views read the SAME raw slice
   `dsum2 (lane_reader 128 32 x k) 0 32`; they differ only by the tc decode.
   ========================================================================== *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
let lemma_to_i32x4_val (x: t_e_int32x4_t) (k: nat{k < 4})
  : Lemma (v (Funarr.impl_5__get (mk_u64 4) #i32 (Canon.to_i32x4 x) (mk_u64 k)) ==
           IVi.tc_of_u Int.I32 (IVi.dsum2 (IVi.lane_reader (mk_u64 128) 32 x (mk_u64 k)) 0 32)) =
  reveal_opaque (`%IVi.to_iv) (IVi.to_iv);
  let reader = IVi.lane_reader (mk_u64 128) 32 x (mk_u64 k) in
  IVi.dsum2_bound reader 0 32;
  IVi.lemma_tc_range Int.I32 (IVi.dsum2 reader 0 32)

let lemma_to_u32x4_val (x: t_e_uint32x4_t) (k: nat{k < 4})
  : Lemma (v (Funarr.impl_5__get (mk_u64 4) #u32 (NV.to_u32x4 x) (mk_u64 k)) ==
           IVi.dsum2 (IVi.lane_reader (mk_u64 128) 32 x (mk_u64 k)) 0 32) =
  reveal_opaque (`%IVi.to_iv) (IVi.to_iv);
  let reader = IVi.lane_reader (mk_u64 128) 32 x (mk_u64 k) in
  IVi.dsum2_bound reader 0 32;
  IVi.lemma_tc_range Int.U32 (IVi.dsum2 reader 0 32)
#pop-options

(* Per-lane signedness bridge between the i32x4 and u32x4 views of the same reg
   (mirrors the pcm `e_vreinterpret_i32_u32_lane_bridge`; consumed by compress). *)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 200"
let e_vreinterpret_i32_u32_lane_bridge (x: BV.t_BitVec (mk_u64 128)) (k: nat{k < 4})
  : Lemma
      (v (get_lane_i32x4 x k) ==
         (let u = v (get_lane_u32x4 x k) in if u < pow2 31 then u else u - pow2 32) /\
       v (get_lane_u32x4 x k) == (v (get_lane_i32x4 x k)) % pow2 32) =
  lemma_to_i32x4_val x k;
  lemma_to_u32x4_val x k;
  let raw = IVi.dsum2 (IVi.lane_reader (mk_u64 128) 32 x (mk_u64 k)) 0 32 in
  assert_norm (Int.bits Int.I32 == 32);
  Canon.lemma_tc_mod Int.I32 raw
#pop-options

(* ============================================================================
   TIER B — logical ops (vandq / veorq).  `ArmIV.vOPq_*` is a BIT-LEVEL
   `impl_9__from_fn 128`, so the codec-commute is proven bit-by-bit, mirroring
   `Intrinsics_views.lemma_and_i16x16_iv` at width 128:  per-bit readback (raw
   bit of the interpreted op == bit-op of operand bits) + `get_bit_OP` + bit-
   extensionality.  Needs the width-128 `impl_9__from_fn` index port (the width-
   256 `lemma_impl9_index` / `lemma_from_fn_lane_reader` don't apply at 128;
   `Canon.lemma_bv_index_n` is already width-generic).
   ========================================================================== *)

(* width-128 port of `Intrinsics_views.lemma_impl9_index` (the `on_domain` reduces). *)
let lemma_impl9_index_128 (f: (i: u64{v i < 128}) -> Bit.t_Bit) (k: u64{v k < 128})
    : Lemma (Funarr.impl_5__get (mk_u64 128) #Bit.t_Bit
               (Libcrux_core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 128)
                  #(u64 -> Bit.t_Bit) f)._0 k == f k) = ()

(* raw underlying-FunArray bit `k` of the interpreted `vandq_s16` is the and of
   the operands' bits `k` (mirror `lemma_and_funarr`, width 128). *)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 200"
let lemma_vandq_funarr_128 (a b: BV.t_BitVec (mk_u64 128)) (k: u64{v k < 128})
    : Lemma (Funarr.impl_5__get (mk_u64 128) #Bit.t_Bit (ArmIV.vandq_s16 a b)._0 k ==
             (match Funarr.impl_5__get (mk_u64 128) #Bit.t_Bit a._0 k,
                    Funarr.impl_5__get (mk_u64 128) #Bit.t_Bit b._0 k
              with
              | Bit.Bit_One, Bit.Bit_One -> Bit.Bit_One
              | _ -> Bit.Bit_Zero)) =
  let f : (i: u64{v i < 128}) -> Bit.t_Bit =
    fun i -> (let i:u64 = i in
              match (a.[ i ] <: Bit.t_Bit), (b.[ i ] <: Bit.t_Bit) with
              | Bit.Bit_One, Bit.Bit_One -> Bit.Bit_One
              | _ -> Bit.Bit_Zero) in
  assert (ArmIV.vandq_s16 a b ==
          Libcrux_core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 128) #(u64 -> Bit.t_Bit) f)
    by (FStar.Tactics.norm [delta_only [`%ArmIV.vandq_s16]; iota; zeta; primops];
        FStar.Tactics.trefl ());
  lemma_impl9_index_128 f k;
  Canon.lemma_bv_index_n #(mk_u64 128) a k;
  Canon.lemma_bv_index_n #(mk_u64 128) b k
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 200"
let lemma_vandq_raw_128 (a b: BV.t_BitVec (mk_u64 128)) (ii: u64{v ii < 8}) (bb: nat{bb < 16})
    : Lemma (IVi.bval (IVi.lane_reader (mk_u64 128) 16 (ArmIV.vandq_s16 a b) ii bb) ==
             Int.bit_and (IVi.bval (IVi.lane_reader (mk_u64 128) 16 a ii bb))
                         (IVi.bval (IVi.lane_reader (mk_u64 128) 16 b ii bb))) =
  assert (16 * v ii + bb < 128);
  lemma_vandq_funarr_128 a b (mk_u64 (16 * v ii + bb))
#pop-options

(* i16-lane commutation for the interpreted vandq: decode ∘ bitwise-and == `&.`. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"
let lemma_vandq_s16_i16x8_iv (a b: BV.t_BitVec (mk_u64 128)) (i: nat{i < 8})
    : Lemma (Funarr.impl_5__get (mk_u64 8) #i16 (Canon.to_i16x8 (ArmIV.vandq_s16 a b)) (mk_u64 i) ==
             ((Funarr.impl_5__get (mk_u64 8) #i16 (Canon.to_i16x8 a) (mk_u64 i)) &.
              (Funarr.impl_5__get (mk_u64 8) #i16 (Canon.to_i16x8 b) (mk_u64 i)))) =
  let aANDb = ArmIV.vandq_s16 a b in
  let ya : i16 = Funarr.impl_5__get (mk_u64 8) #i16 (Canon.to_i16x8 a) (mk_u64 i) in
  let yb : i16 = Funarr.impl_5__get (mk_u64 8) #i16 (Canon.to_i16x8 b) (mk_u64 i) in
  let yr : i16 = Funarr.impl_5__get (mk_u64 8) #i16 (Canon.to_i16x8 aANDb) (mk_u64 i) in
  let aux (bb: usize{v bb < 16})
      : Lemma (Int.get_bit #Int.I16 yr bb == Int.get_bit #Int.I16 (ya &. yb) bb) =
    Canon.lemma_readback Int.I16 (mk_u64 128) (mk_u64 8) aANDb (mk_u64 i) (v bb);
    Canon.lemma_readback Int.I16 (mk_u64 128) (mk_u64 8) a (mk_u64 i) (v bb);
    Canon.lemma_readback Int.I16 (mk_u64 128) (mk_u64 8) b (mk_u64 i) (v bb);
    lemma_vandq_raw_128 a b (mk_u64 i) (v bb);
    Int.get_bit_and #Int.I16 ya yb bb
  in
  Classical.forall_intro aux;
  Int.lemma_int_t_eq_via_bits #Int.I16 yr (ya &. yb)
#pop-options

(* companion op-fact: i16x8 view of the (hardware) vandq_s16. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"
let lemma_e_vandq_s16 (a b: t_e_int16x8_t)
  : Lemma (vec128_as_i16x8 (e_vandq_s16 a b)
           == Spec.Utils.map2 ( &. ) (vec128_as_i16x8 a) (vec128_as_i16x8 b))
          [SMTPat (vec128_as_i16x8 (e_vandq_s16 a b))] =
  let r = e_vandq_s16 a b in
  let aux (i: nat{i < 8})
      : Lemma (Seq.index (vec128_as_i16x8 r) i ==
               Seq.index (Spec.Utils.map2 ( &. ) (vec128_as_i16x8 a) (vec128_as_i16x8 b)) i) =
    NV.lemma_vandq_s16 a b;
    lemma_vandq_s16_i16x8_iv a b i
  in
  Classical.forall_intro aux;
  Seq.lemma_eq_intro (vec128_as_i16x8 r)
    (Spec.Utils.map2 ( &. ) (vec128_as_i16x8 a) (vec128_as_i16x8 b))
#pop-options

(* vandq_u16 / vandq_u32 reuse the SAME bit-and funarr fact: ArmIV.vandq_u16 and
   ArmIV.vandq_u32 both delegate to ArmIV.vandq_s16.  Only the lane VIEW (u16x8 /
   u32x4) + lane width for the raw-bit fact change. *)

(* 32-bit-lane raw-bit variant (for the u32x4 view) reusing lemma_vandq_funarr_128. *)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 200"
let lemma_vandq_raw32_128 (a b: BV.t_BitVec (mk_u64 128)) (ii: u64{v ii < 4}) (bb: nat{bb < 32})
    : Lemma (IVi.bval (IVi.lane_reader (mk_u64 128) 32 (ArmIV.vandq_s16 a b) ii bb) ==
             Int.bit_and (IVi.bval (IVi.lane_reader (mk_u64 128) 32 a ii bb))
                         (IVi.bval (IVi.lane_reader (mk_u64 128) 32 b ii bb))) =
  assert (32 * v ii + bb < 128);
  lemma_vandq_funarr_128 a b (mk_u64 (32 * v ii + bb))
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"
let lemma_vandq_u16_u16x8_iv (a b: BV.t_BitVec (mk_u64 128)) (i: nat{i < 8})
    : Lemma (Funarr.impl_5__get (mk_u64 8) #u16 (NV.to_u16x8 (ArmIV.vandq_u16 a b)) (mk_u64 i) ==
             ((Funarr.impl_5__get (mk_u64 8) #u16 (NV.to_u16x8 a) (mk_u64 i)) &.
              (Funarr.impl_5__get (mk_u64 8) #u16 (NV.to_u16x8 b) (mk_u64 i)))) =
  let r = ArmIV.vandq_u16 a b in
  let ya : u16 = Funarr.impl_5__get (mk_u64 8) #u16 (NV.to_u16x8 a) (mk_u64 i) in
  let yb : u16 = Funarr.impl_5__get (mk_u64 8) #u16 (NV.to_u16x8 b) (mk_u64 i) in
  let yr : u16 = Funarr.impl_5__get (mk_u64 8) #u16 (NV.to_u16x8 r) (mk_u64 i) in
  let aux (bb: usize{v bb < 16})
      : Lemma (Int.get_bit #Int.U16 yr bb == Int.get_bit #Int.U16 (ya &. yb) bb) =
    Canon.lemma_readback Int.U16 (mk_u64 128) (mk_u64 8) r (mk_u64 i) (v bb);
    Canon.lemma_readback Int.U16 (mk_u64 128) (mk_u64 8) a (mk_u64 i) (v bb);
    Canon.lemma_readback Int.U16 (mk_u64 128) (mk_u64 8) b (mk_u64 i) (v bb);
    lemma_vandq_raw_128 a b (mk_u64 i) (v bb);
    Int.get_bit_and #Int.U16 ya yb bb
  in
  Classical.forall_intro aux;
  Int.lemma_int_t_eq_via_bits #Int.U16 yr (ya &. yb)
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"
let lemma_e_vandq_u16 (a b: t_e_uint16x8_t)
  : Lemma (vec128_as_u16x8 (e_vandq_u16 a b)
           == Spec.Utils.map2 ( &. ) (vec128_as_u16x8 a) (vec128_as_u16x8 b))
          [SMTPat (vec128_as_u16x8 (e_vandq_u16 a b))] =
  let r = e_vandq_u16 a b in
  let aux (i: nat{i < 8})
      : Lemma (Seq.index (vec128_as_u16x8 r) i ==
               Seq.index (Spec.Utils.map2 ( &. ) (vec128_as_u16x8 a) (vec128_as_u16x8 b)) i) =
    NV.lemma_vandq_u16 a b;
    lemma_vandq_u16_u16x8_iv a b i
  in
  Classical.forall_intro aux;
  Seq.lemma_eq_intro (vec128_as_u16x8 r)
    (Spec.Utils.map2 ( &. ) (vec128_as_u16x8 a) (vec128_as_u16x8 b))
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"
let lemma_vandq_u32_u32x4_iv (a b: BV.t_BitVec (mk_u64 128)) (i: nat{i < 4})
    : Lemma (Funarr.impl_5__get (mk_u64 4) #u32 (NV.to_u32x4 (ArmIV.vandq_u32 a b)) (mk_u64 i) ==
             ((Funarr.impl_5__get (mk_u64 4) #u32 (NV.to_u32x4 a) (mk_u64 i)) &.
              (Funarr.impl_5__get (mk_u64 4) #u32 (NV.to_u32x4 b) (mk_u64 i)))) =
  let r = ArmIV.vandq_u32 a b in
  let ya : u32 = Funarr.impl_5__get (mk_u64 4) #u32 (NV.to_u32x4 a) (mk_u64 i) in
  let yb : u32 = Funarr.impl_5__get (mk_u64 4) #u32 (NV.to_u32x4 b) (mk_u64 i) in
  let yr : u32 = Funarr.impl_5__get (mk_u64 4) #u32 (NV.to_u32x4 r) (mk_u64 i) in
  let aux (bb: usize{v bb < 32})
      : Lemma (Int.get_bit #Int.U32 yr bb == Int.get_bit #Int.U32 (ya &. yb) bb) =
    Canon.lemma_readback Int.U32 (mk_u64 128) (mk_u64 4) r (mk_u64 i) (v bb);
    Canon.lemma_readback Int.U32 (mk_u64 128) (mk_u64 4) a (mk_u64 i) (v bb);
    Canon.lemma_readback Int.U32 (mk_u64 128) (mk_u64 4) b (mk_u64 i) (v bb);
    lemma_vandq_raw32_128 a b (mk_u64 i) (v bb);
    Int.get_bit_and #Int.U32 ya yb bb
  in
  Classical.forall_intro aux;
  Int.lemma_int_t_eq_via_bits #Int.U32 yr (ya &. yb)
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"
let lemma_e_vandq_u32 (a b: t_e_uint32x4_t)
  : Lemma (vec128_as_u32x4 (e_vandq_u32 a b)
           == Spec.Utils.map2 ( &. ) (vec128_as_u32x4 a) (vec128_as_u32x4 b))
          [SMTPat (vec128_as_u32x4 (e_vandq_u32 a b))] =
  let r = e_vandq_u32 a b in
  let aux (i: nat{i < 4})
      : Lemma (Seq.index (vec128_as_u32x4 r) i ==
               Seq.index (Spec.Utils.map2 ( &. ) (vec128_as_u32x4 a) (vec128_as_u32x4 b)) i) =
    NV.lemma_vandq_u32 a b;
    lemma_vandq_u32_u32x4_iv a b i
  in
  Classical.forall_intro aux;
  Seq.lemma_eq_intro (vec128_as_u32x4 r)
    (Spec.Utils.map2 ( &. ) (vec128_as_u32x4 a) (vec128_as_u32x4 b))
#pop-options

(* ── veorq_s16 (XOR): own bit-level funarr/raw (Zero,Zero->Zero | One,One->Zero | _->One) *)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 200"
let lemma_veorq_funarr_128 (a b: BV.t_BitVec (mk_u64 128)) (k: u64{v k < 128})
    : Lemma (Funarr.impl_5__get (mk_u64 128) #Bit.t_Bit (ArmIV.veorq_s16 a b)._0 k ==
             (match Funarr.impl_5__get (mk_u64 128) #Bit.t_Bit a._0 k,
                    Funarr.impl_5__get (mk_u64 128) #Bit.t_Bit b._0 k
              with
              | Bit.Bit_Zero, Bit.Bit_Zero -> Bit.Bit_Zero
              | Bit.Bit_One, Bit.Bit_One -> Bit.Bit_Zero
              | _ -> Bit.Bit_One)) =
  let f : (i: u64{v i < 128}) -> Bit.t_Bit =
    fun i -> (let i:u64 = i in
              match (a.[ i ] <: Bit.t_Bit), (b.[ i ] <: Bit.t_Bit) with
              | Bit.Bit_Zero, Bit.Bit_Zero -> Bit.Bit_Zero
              | Bit.Bit_One, Bit.Bit_One -> Bit.Bit_Zero
              | _ -> Bit.Bit_One) in
  assert (ArmIV.veorq_s16 a b ==
          Libcrux_core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 128) #(u64 -> Bit.t_Bit) f)
    by (FStar.Tactics.norm [delta_only [`%ArmIV.veorq_s16]; iota; zeta; primops];
        FStar.Tactics.trefl ());
  lemma_impl9_index_128 f k;
  Canon.lemma_bv_index_n #(mk_u64 128) a k;
  Canon.lemma_bv_index_n #(mk_u64 128) b k
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 200"
let lemma_veorq_raw_128 (a b: BV.t_BitVec (mk_u64 128)) (ii: u64{v ii < 8}) (bb: nat{bb < 16})
    : Lemma (IVi.bval (IVi.lane_reader (mk_u64 128) 16 (ArmIV.veorq_s16 a b) ii bb) ==
             Int.bit_xor (IVi.bval (IVi.lane_reader (mk_u64 128) 16 a ii bb))
                         (IVi.bval (IVi.lane_reader (mk_u64 128) 16 b ii bb))) =
  assert (16 * v ii + bb < 128);
  lemma_veorq_funarr_128 a b (mk_u64 (16 * v ii + bb))
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"
let lemma_veorq_s16_i16x8_iv (a b: BV.t_BitVec (mk_u64 128)) (i: nat{i < 8})
    : Lemma (Funarr.impl_5__get (mk_u64 8) #i16 (Canon.to_i16x8 (ArmIV.veorq_s16 a b)) (mk_u64 i) ==
             ((Funarr.impl_5__get (mk_u64 8) #i16 (Canon.to_i16x8 a) (mk_u64 i)) ^.
              (Funarr.impl_5__get (mk_u64 8) #i16 (Canon.to_i16x8 b) (mk_u64 i)))) =
  let aXORb = ArmIV.veorq_s16 a b in
  let ya : i16 = Funarr.impl_5__get (mk_u64 8) #i16 (Canon.to_i16x8 a) (mk_u64 i) in
  let yb : i16 = Funarr.impl_5__get (mk_u64 8) #i16 (Canon.to_i16x8 b) (mk_u64 i) in
  let yr : i16 = Funarr.impl_5__get (mk_u64 8) #i16 (Canon.to_i16x8 aXORb) (mk_u64 i) in
  let aux (bb: usize{v bb < 16})
      : Lemma (Int.get_bit #Int.I16 yr bb == Int.get_bit #Int.I16 (ya ^. yb) bb) =
    Canon.lemma_readback Int.I16 (mk_u64 128) (mk_u64 8) aXORb (mk_u64 i) (v bb);
    Canon.lemma_readback Int.I16 (mk_u64 128) (mk_u64 8) a (mk_u64 i) (v bb);
    Canon.lemma_readback Int.I16 (mk_u64 128) (mk_u64 8) b (mk_u64 i) (v bb);
    lemma_veorq_raw_128 a b (mk_u64 i) (v bb);
    Int.get_bit_xor #Int.I16 ya yb bb
  in
  Classical.forall_intro aux;
  Int.lemma_int_t_eq_via_bits #Int.I16 yr (ya ^. yb)
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"
let lemma_e_veorq_s16 (a b: t_e_int16x8_t)
  : Lemma (vec128_as_i16x8 (e_veorq_s16 a b)
           == Spec.Utils.map2 ( ^. ) (vec128_as_i16x8 a) (vec128_as_i16x8 b))
          [SMTPat (vec128_as_i16x8 (e_veorq_s16 a b))] =
  let r = e_veorq_s16 a b in
  let aux (i: nat{i < 8})
      : Lemma (Seq.index (vec128_as_i16x8 r) i ==
               Seq.index (Spec.Utils.map2 ( ^. ) (vec128_as_i16x8 a) (vec128_as_i16x8 b)) i) =
    NV.lemma_veorq_s16 a b;
    lemma_veorq_s16_i16x8_iv a b i
  in
  Classical.forall_intro aux;
  Seq.lemma_eq_intro (vec128_as_i16x8 r)
    (Spec.Utils.map2 ( ^. ) (vec128_as_i16x8 a) (vec128_as_i16x8 b))
#pop-options
