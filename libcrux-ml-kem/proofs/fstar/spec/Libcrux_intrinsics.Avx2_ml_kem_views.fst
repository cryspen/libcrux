module Libcrux_intrinsics.Avx2_ml_kem_views
#set-options "--fuel 0 --ifuel 1 --z3rlimit 50"
open FStar.Mul
open Core_models
open Libcrux_intrinsics.Avx2

(* Canonical Option-B intrinsics view + PROVEN op-lemmas (Phase-3 A-on-B adapter). *)
module Funarr = Libcrux_core_models.Abstractions.Funarr
module Canon  = Libcrux_core_models.Intrinsics_views
module IV     = Libcrux_core_models.Core_arch.X86.Interpretations.Int_vec
module Avx2c  = Libcrux_core_models.Core_arch.X86.Avx2
module Sse2c  = Libcrux_core_models.Core_arch.X86.Sse2

(* ============================================================================
   ml-kem AVX2 lane-view + per-op fact companion (core-models migration).

   HISTORY.  This module was originally a small file holding five ml-kem-only
   SMTPat view-axioms relocated out of the shared `Libcrux_intrinsics.Avx2_extract`
   interface (2026-06-30).  As part of the `intrinsics-cm-migration` campaign
   (2026-07-28) it becomes the SINGLE ml-kem lane-view/fact companion over the
   REAL `Libcrux_intrinsics.Avx2` ops (which rest on the differentially-tested
   `libcrux-core-models` model), replacing the hand-written, untested pcm
   `Libcrux_intrinsics.Avx2_extract` (bit_vec) intrinsics model.

   DESIGN (clean ml-dsa-style; NO `Avx2_extract` shim).  The lane VIEWS
   (`vec256_as_i16x16` / `get_lane` / `lane32` / ...) and per-op FACT lemmas that
   the pcm `Avx2_extract.fsti` carried as op `ensures` are MOVED here, phrased
   over the real ops (`open Libcrux_intrinsics.Avx2`).  The op BODIES come from
   the real `Avx2` (core-models `e_mm256_OP`); this module only re-exposes the
   lane-view fact surface ml-kem's proofs consume.

   TRUST.  Every fact lemma below is `admit ()` at P1 (skeleton), tagged
   `[@@ "trusted: validated-axiom ..."]`.  This PRESERVES the pcm trust footprint
   EXACTLY: pcm's views were abstract `val`, its op facts were assumed `#[ensures]`
   / `admit ()`.  P1 is therefore admit-NEUTRAL, not a regression.  P2 replaces
   each `admit ()` with a proof over core-models `to_i16x16` + the `Int_vec.Lemmas`
   lift lemma + the (P2) round-trip lemma.  The views keep ml-kem's Seq/Array shape
   (`vec256_as_i16x16 : t_Array i16 (sz 16)`, `get_lane`, `Spec.Utils.map2`) — we
   adopt ml-dsa's STRUCTURE + op-lemma proof technique, NOT its FunArray view type.

   ml-kem uses ONLY the i16x16 / lane32 / vec128 views.  The u64x4 view
   (`vec256_as_u64x4` / `get_lane_u64x4` / `lemma_mm256_*_u64x4`) is sha3-only and
   is NOT declared here.  The bit-level bridges (`bit_vec_of_int_t_array_*`,
   `mm256_{storeu,loadu}_si256_u8` bit_vec, `mm256_cmpgt_epi16` bit-form) are used
   only by top-`Avx2` / `Serialize` / `Sampling`; over core-models the underlying
   `t_BitVec` is a struct (indexable via `t_Index`), not a `bit_vec` FUNCTION, so
   those bridges need a representation adaptation and are authored per-module when
   Serialize/Compress/Sampling are migrated.  Their pcm source is preserved
   verbatim in the DEFERRED block at the bottom of this file.

   This module lives in `proofs/fstar/spec/` (hand-maintained, NOT the
   hax-extraction dir), so `cargo hax into` never clobbers it; it is on ml-kem's
   include path but not sha3's.  See
   ~/hax-fstar-mcp/libcrux-notes/agent-status/sprint-2026-07-28-cm-migration-rollup.md.
   ========================================================================== *)

(* ── Lane-view types + abstract views ─────────────────────────────────────── *)

unfold type t_Vec256 = Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
unfold type t_Vec128 = Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

(* Abstract i16x16 lane view (pcm `val vec256_as_i16x16`).  Uninterpreted at P1;
   semantics carried by the admitted fact-lemmas below (validated by the
   core-models differential tests).  P2 gives it a body = core-models
   `to_i16x16` (FunArray -> t_Array via createi). *)
(* A-on-B adapter: Seq view = per-lane read of the canonical FunArray view. *)
let vec256_as_i16x16 (x: t_Vec256) : t_Array i16 (sz 16) =
  Seq.init 16 (fun i -> Funarr.impl_5__get (mk_u64 16) #i16 (Canon.to_i16x16 x) (mk_u64 i))
let get_lane (v: t_Vec256) (i:nat{i < 16}) = Seq.index (vec256_as_i16x16 v) i

(* One-line Seq<->FunArray index iso (Seq.init index). *)
let vec256_index (x: t_Vec256) (i: nat{i < 16})
  : Lemma (Seq.index (vec256_as_i16x16 x) i
           == Funarr.impl_5__get (mk_u64 16) #i16 (Canon.to_i16x16 x) (mk_u64 i))
          [SMTPat (Seq.index (vec256_as_i16x16 x) i)]
  = ()

(* Reduction of an Int_vec FunArray produced by `from_fn 16` at a Seq index. *)
let index_from_fn16 (#t: Type0) (g: (i: u64{v i < 16}) -> t) (i: nat{i < 16})
  : Lemma (Funarr.impl_5__get (mk_u64 16) #t
             (Funarr.impl_5__from_fn (mk_u64 16) #t #(u64 -> t) g) (mk_u64 i)
           == g (mk_u64 i))
  = ()

let index_from_fn8 (#t: Type0) (g: (i: u64{v i < 8}) -> t) (i: nat{i < 8})
  : Lemma (Funarr.impl_5__get (mk_u64 8) #t
             (Funarr.impl_5__from_fn (mk_u64 8) #t #(u64 -> t) g) (mk_u64 i)
           == g (mk_u64 i))
  = ()

(* Signed value of the 32-bit lane `j` (low half = i16 lane 2j, high = 2j+1). *)
let lane32 (vec: t_Vec256) (j: nat{j < 8}) : int =
  (Rust_primitives.Integers.v (get_lane vec (2 * j)) % 65536) +
  65536 * Rust_primitives.Integers.v (get_lane vec (2 * j + 1))

(* Unsigned value of the 64-bit lane `i` (mm256_mul_epu32 output). *)
let lane64u (vec: t_Vec256) (i: nat{i < 4}) : int =
  (lane32 vec (2 * i) % 4294967296) + 4294967296 * (lane32 vec (2 * i + 1) % 4294967296)

(* Signed saturation into the i16 range (mm256_packs_epi32 per-lane clamp). *)
let sat_i16 (x: int) : i16 =
  if x > 32767 then mk_i16 32767
  else if x < (-32768) then mk_i16 (-32768)
  else mk_i16 x

(* Lane-permutation index helpers (opaque so they stay atomic under op-ensures
   foralls; consumers `reveal_opaque` inside small clean per-control lemmas). *)
[@@ "opaque_to_smt"]
let shuffle32_src (c: i32) (l: nat{l < 8}) : (s:nat{s < 8}) =
  let cb = (Rust_primitives.Integers.v c) % 256 in
  (l / 4) * 4 + ((match l % 4 with | 0 -> cb | 1 -> cb / 4 | 2 -> cb / 16 | _ -> cb / 64) % 4)

[@@ "opaque_to_smt"]
let permute64_src (c: i32) (q: nat{q < 4}) : (s:nat{s < 4}) =
  let cb = (Rust_primitives.Integers.v c) % 256 in
  (match q with | 0 -> cb | 1 -> cb / 4 | 2 -> cb / 16 | _ -> cb / 64) % 4

[@@ "opaque_to_smt"]
let blend_sel (c: i32) (k: nat{k < 16}) : bool =
  let cb = (Rust_primitives.Integers.v c) % 256 in
  ((match k % 8 with | 0 -> cb | 1 -> cb / 2 | 2 -> cb / 4 | 3 -> cb / 8
                     | 4 -> cb / 16 | 5 -> cb / 32 | 6 -> cb / 64 | _ -> cb / 128) % 2) = 1

(* i16x8 lane view of a 128-bit vector (A-on-B adapter over canonical to_i16x8). *)
let vec128_as_i16x8 (x: t_Vec128) : t_Array i16 (sz 8) =
  Seq.init 8 (fun i -> Funarr.impl_5__get (mk_u64 8) #i16 (Canon.to_i16x8 x) (mk_u64 i))
let get_lane128 (v: t_Vec128) (i:nat{i < 8}) = Seq.index (vec128_as_i16x8 v) i

let vec128_index (x: t_Vec128) (i: nat{i < 8})
  : Lemma (Seq.index (vec128_as_i16x8 x) i
           == Funarr.impl_5__get (mk_u64 8) #i16 (Canon.to_i16x8 x) (mk_u64 i))
          [SMTPat (Seq.index (vec128_as_i16x8 x) i)]
  = ()

(* ── i16x16-view arithmetic/logical facts ─────────────────────────────────── *)

[@@ "trusted: validated-axiom: i16x16 view of mm256_add_epi16 (core-models differential-tested)"]
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_mm256_add_epi16 (lhs rhs: t_Vec256)
  : Lemma (vec256_as_i16x16 (mm256_add_epi16 lhs rhs)
           == Spec.Utils.map2 ( +. ) (vec256_as_i16x16 lhs) (vec256_as_i16x16 rhs))
          [SMTPat (vec256_as_i16x16 (mm256_add_epi16 lhs rhs))] =
  reveal_opaque (`%mm256_add_epi16) mm256_add_epi16;
  Canon.lemma_mm256_add_epi16 lhs rhs;
  Seq.lemma_eq_intro (vec256_as_i16x16 (mm256_add_epi16 lhs rhs))
                     (Spec.Utils.map2 ( +. ) (vec256_as_i16x16 lhs) (vec256_as_i16x16 rhs))
#pop-options

[@@ "trusted: validated-axiom: i16x16 view of mm256_sub_epi16 (core-models differential-tested)"]
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_mm256_sub_epi16 (lhs rhs: t_Vec256)
  : Lemma (vec256_as_i16x16 (mm256_sub_epi16 lhs rhs)
           == Spec.Utils.map2 ( -. ) (vec256_as_i16x16 lhs) (vec256_as_i16x16 rhs))
          [SMTPat (vec256_as_i16x16 (mm256_sub_epi16 lhs rhs))] =
  reveal_opaque (`%mm256_sub_epi16) mm256_sub_epi16;
  Canon.lemma_mm256_sub_epi16 lhs rhs;
  Seq.lemma_eq_intro (vec256_as_i16x16 (mm256_sub_epi16 lhs rhs))
                     (Spec.Utils.map2 ( -. ) (vec256_as_i16x16 lhs) (vec256_as_i16x16 rhs))
#pop-options

[@@ "trusted: validated-axiom: i16x16 view of mm256_mullo_epi16 (core-models differential-tested)"]
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_mm256_mullo_epi16 (v1 v2: t_Vec256)
  : Lemma (vec256_as_i16x16 (mm256_mullo_epi16 v1 v2)
           == Spec.Utils.map2 mul_mod (vec256_as_i16x16 v1) (vec256_as_i16x16 v2))
          [SMTPat (vec256_as_i16x16 (mm256_mullo_epi16 v1 v2))] =
  reveal_opaque (`%mm256_mullo_epi16) mm256_mullo_epi16;
  Canon.lemma_mm256_mullo_epi16 v1 v2;
  Seq.lemma_eq_intro (vec256_as_i16x16 (mm256_mullo_epi16 v1 v2))
                     (Spec.Utils.map2 mul_mod (vec256_as_i16x16 v1) (vec256_as_i16x16 v2))
#pop-options

[@@ "trusted: validated-axiom: i16x16 view of mm256_mulhi_epi16 (core-models differential-tested)"]
#push-options "--fuel 2 --ifuel 1 --z3rlimit 200"
let lemma_mm256_mulhi_epi16 (lhs rhs: t_Vec256)
  : Lemma (vec256_as_i16x16 (mm256_mulhi_epi16 lhs rhs)
           == Spec.Utils.map2 (fun x y ->
                cast (((cast x <: i32) *. (cast y <: i32)) >>! (mk_i32 16)) <: i16)
              (vec256_as_i16x16 lhs)
              (vec256_as_i16x16 rhs))
          [SMTPat (vec256_as_i16x16 (mm256_mulhi_epi16 lhs rhs))] =
  reveal_opaque (`%mm256_mulhi_epi16) mm256_mulhi_epi16;
  Canon.lemma_mm256_mulhi_epi16 lhs rhs;
  Seq.lemma_eq_intro (vec256_as_i16x16 (mm256_mulhi_epi16 lhs rhs))
              (Spec.Utils.map2 (fun x y ->
                cast (((cast x <: i32) *. (cast y <: i32)) >>! (mk_i32 16)) <: i16)
              (vec256_as_i16x16 lhs)
              (vec256_as_i16x16 rhs))
#pop-options

(* PROVEN over core-models: reveal the intrinsic to the hardware op, then the
   canonical shared per-lane `and` commutation (`Canon.lemma_and_i16x16`, itself
   a proven i16 slice/decode commutation on top of the differentially-tested raw
   `and` lift). *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"
let lemma_mm256_and_si256 (lhs rhs: t_Vec256)
  : Lemma (vec256_as_i16x16 (mm256_and_si256 lhs rhs)
           == Spec.Utils.map2 ( &. ) (vec256_as_i16x16 lhs) (vec256_as_i16x16 rhs))
          [SMTPat (vec256_as_i16x16 (mm256_and_si256 lhs rhs))] =
  reveal_opaque (`%mm256_and_si256) mm256_and_si256;
  let r = mm256_and_si256 lhs rhs in
  let aux (i: nat{i < 16})
      : Lemma (Seq.index (vec256_as_i16x16 r) i ==
               Seq.index (Spec.Utils.map2 ( &. ) (vec256_as_i16x16 lhs) (vec256_as_i16x16 rhs)) i) =
    Canon.lemma_and_i16x16 lhs rhs i
  in
  Classical.forall_intro aux;
  Seq.lemma_eq_intro (vec256_as_i16x16 r)
    (Spec.Utils.map2 ( &. ) (vec256_as_i16x16 lhs) (vec256_as_i16x16 rhs))
#pop-options

(* ml-kem i16-view characterization of mm256_xor (called explicitly by Compress;
   also SMTPat).  Coexists with sha3's u64x4-view of the same op. *)
[@@ "trusted: validated-axiom: i16x16 view of mm256_xor_si256 (core-models differential-tested)"]
let lemma_mm256_xor_si256 (lhs rhs: t_Vec256)
  : Lemma (vec256_as_i16x16 (mm256_xor_si256 lhs rhs)
           == Spec.Utils.map2 (^.) (vec256_as_i16x16 lhs) (vec256_as_i16x16 rhs))
          [SMTPat (vec256_as_i16x16 (mm256_xor_si256 lhs rhs))] = admit ()

[@@ "trusted: validated-axiom: i16x16 view of mm256_set1_epi16 (core-models differential-tested)"]
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_mm256_set1_epi16 (constant: i16)
  : Lemma (vec256_as_i16x16 (mm256_set1_epi16 constant) == Spec.Utils.create (sz 16) constant)
          [SMTPat (vec256_as_i16x16 (mm256_set1_epi16 constant))] =
  reveal_opaque (`%mm256_set1_epi16) mm256_set1_epi16;
  Canon.lemma_mm256_set1_epi16 constant;
  Seq.lemma_eq_intro (vec256_as_i16x16 (mm256_set1_epi16 constant))
                     (Spec.Utils.create (sz 16) constant)
#pop-options

[@@ "trusted: validated-axiom: i16x16 view of mm256_set_epi16 (core-models differential-tested)"]
let lemma_mm256_set_epi16 v15 v14 v13 v12 v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0
  : Lemma (vec256_as_i16x16 (mm256_set_epi16 v15 v14 v13 v12 v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0)
           == Spec.Utils.create16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
          [SMTPat (vec256_as_i16x16 (mm256_set_epi16 v15 v14 v13 v12 v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0))]
  = admit ()

(* NB: NO SMTPat.  `mm256_setzero_si256 ()` is a fully GROUND core-models
   `t_BitVec` term, so an SMTPat on `vec256_as_i16x16 (mm256_setzero_si256 ())`
   is a variable-free trigger → Z3 emits "pattern does not contain any variable",
   which corrupts F*'s output parse into an Error 276 (whereas under pcm the
   `bit_vec` result carried a variable).  Consumers call this explicitly. *)
[@@ "trusted: validated-axiom: i16x16 view of mm256_setzero_si256 (core-models differential-tested)"]
let lemma_mm256_setzero_si256 (u: Prims.unit)
  : Lemma (vec256_as_i16x16 (mm256_setzero_si256 ()) == Seq.create 16 (mk_i16 0)) = admit ()

[@@ "trusted: validated-axiom: i16x16 view of mm256_srai_epi16 (core-models differential-tested)"]
#push-options "--fuel 2 --ifuel 1 --z3rlimit 200"
let lemma_mm256_srai_epi16 (v_SHIFT_BY: i32) (vector: t_Vec256)
  : Lemma (requires v_SHIFT_BY >=. mk_i32 0 /\ v_SHIFT_BY <. mk_i32 16)
          (ensures vec256_as_i16x16 (mm256_srai_epi16 v_SHIFT_BY vector)
                   == Spec.Utils.map_array (fun x -> x >>! v_SHIFT_BY) (vec256_as_i16x16 vector))
          [SMTPat (vec256_as_i16x16 (mm256_srai_epi16 v_SHIFT_BY vector))] =
  reveal_opaque (`%mm256_srai_epi16) mm256_srai_epi16;
  Canon.lemma_mm256_srai_epi16 v_SHIFT_BY vector;
  Seq.lemma_eq_intro (vec256_as_i16x16 (mm256_srai_epi16 v_SHIFT_BY vector))
                   (Spec.Utils.map_array (fun x -> x >>! v_SHIFT_BY) (vec256_as_i16x16 vector))
#pop-options

(* ml-kem i16-view of the logical right shift (called explicitly by Compress,
   e.g. lemma_mm256_srli_epi16_15; also SMTPat). *)
[@@ "trusted: validated-axiom: i16x16 view of mm256_srli_epi16 (core-models differential-tested)"]
let lemma_mm256_srli_epi16 (v_SHIFT_BY: i32 {v v_SHIFT_BY >= 0 /\ v v_SHIFT_BY < 16}) (vector: t_Vec256)
  : Lemma (vec256_as_i16x16 (mm256_srli_epi16 v_SHIFT_BY vector)
           == Spec.Utils.map_array (fun (x:i16) -> cast ((cast x <: u16) >>! v_SHIFT_BY) <: i16)
                (vec256_as_i16x16 vector))
          [SMTPat (vec256_as_i16x16 (mm256_srli_epi16 v_SHIFT_BY vector))] = admit ()

(* ── cross-width bridge wrapper + lane32-half helper (Phase-3 gap-2) ───────── *)

(* thin ml-kem wrapper over the crate-independent canonical bridge: the i16-pair
   `lane32` value equals the native i32 decode of the same 32 bits. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 60"
let lemma_lane32_eq_to_i32x8 (vec: t_Vec256) (j: nat{j < 8})
  : Lemma (lane32 vec j ==
           Rust_primitives.Integers.v
             (Funarr.impl_5__get (mk_u64 8) #i32 (Canon.to_i32x8 vec) (mk_u64 j))) =
  assert_norm (pow2 16 == 65536);
  Canon.lemma_lane32_bridge vec j
#pop-options

(* lane32 decomposes into its two i16 sub-lanes (pure lane32-definition arithmetic;
   re-derived here as Arithmetic_theory.lemma_lane32_halves is a downstream consumer). *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let lemma_halves (w: t_Vec256) (j: nat{j < 8})
  : Lemma ((lane32 w j) @% pow2 16 == Rust_primitives.Integers.v (get_lane w (2 * j)) /\
           (lane32 w j) / pow2 16 == Rust_primitives.Integers.v (get_lane w (2 * j + 1))) =
  let lo = Rust_primitives.Integers.v (get_lane w (2 * j)) in
  let hi = Rust_primitives.Integers.v (get_lane w (2 * j + 1)) in
  assert_norm (pow2 16 == 65536);
  FStar.Math.Lemmas.lemma_div_plus (lo % pow2 16) hi (pow2 16);
  FStar.Math.Lemmas.small_div (lo % pow2 16) (pow2 16);
  FStar.Math.Lemmas.modulo_addition_lemma (lo % pow2 16) (pow2 16) hi;
  FStar.Math.Lemmas.small_mod (lo % pow2 16) (pow2 16);
  Spec.Utils.lemma_range_at_percent lo (pow2 16)
#pop-options

(* left-shift by 16 of an i32 lane: the low i16 sub-lane becomes 0, the high i16
   sub-lane becomes the original low i16 (pure integer / modular arithmetic). *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
let lemma_shl16 (w: int)
  : Lemma (ensures (let vv = (w * pow2 16) @% pow2 32 in
                    vv @% pow2 16 == 0 /\ vv / pow2 16 == w @% pow2 16)) =
  assert_norm (pow2 32 == pow2 16 * pow2 16);
  assert_norm (pow2 32 / 2 == pow2 16 * pow2 15);
  assert_norm (pow2 16 == 2 * pow2 15);
  let n16 = pow2 16 in
  let wm = w % n16 in
  FStar.Math.Lemmas.lemma_mod_lt w n16;
  FStar.Math.Lemmas.modulo_scale_lemma w n16 n16;
  if wm >= pow2 15 then begin
    FStar.Math.Lemmas.cancel_mul_div (wm - n16) n16;
    FStar.Math.Lemmas.cancel_mul_mod (wm - n16) n16
  end
  else begin
    FStar.Math.Lemmas.cancel_mul_div wm n16;
    FStar.Math.Lemmas.cancel_mul_mod wm n16
  end
#pop-options

(* ── lane32-view (32-bit lane) facts ──────────────────────────────────────── *)

[@@ "trusted: validated-axiom: lane32 view of mm256_add_epi32 (core-models differential-tested)"]
let lemma_mm256_add_epi32 (lhs rhs: t_Vec256)
  : Lemma (ensures forall (j: nat). j < 8 ==>
             lane32 (mm256_add_epi32 lhs rhs) j == (lane32 lhs j + lane32 rhs j) @% 4294967296)
          [SMTPat (mm256_add_epi32 lhs rhs)] = admit ()

[@@ "trusted: validated-axiom: lane32 view of mm256_mullo_epi32 (core-models differential-tested)"]
let lemma_mm256_mullo_epi32 (lhs rhs: t_Vec256)
  : Lemma (ensures forall (j: nat). j < 8 ==>
             lane32 (mm256_mullo_epi32 lhs rhs) j == (lane32 lhs j * lane32 rhs j) @% 4294967296)
          [SMTPat (mm256_mullo_epi32 lhs rhs)] = admit ()

[@@ "trusted: validated-axiom: lane64u view of mm256_mul_epu32 (core-models differential-tested)"]
let lemma_mm256_mul_epu32 (lhs rhs: t_Vec256)
  : Lemma (ensures forall (i: nat). i < 4 ==>
             lane64u (mm256_mul_epu32 lhs rhs) i ==
             (lane32 lhs (2 * i) % 4294967296) * (lane32 rhs (2 * i) % 4294967296))
          [SMTPat (mm256_mul_epu32 lhs rhs)] = admit ()

[@@ "trusted: validated-axiom: lane32 view of mm256_madd_epi16 (core-models differential-tested)"]
let lemma_madd_epi16_lane32 (lhs rhs: t_Vec256)
  : Lemma (ensures forall (j: nat). j < 8 ==>
             lane32 (mm256_madd_epi16 lhs rhs) j ==
               (Rust_primitives.Integers.v (get_lane lhs (2*j)) * Rust_primitives.Integers.v (get_lane rhs (2*j)) +
                Rust_primitives.Integers.v (get_lane lhs (2*j+1)) * Rust_primitives.Integers.v (get_lane rhs (2*j+1)))
               @% 4294967296)
          [SMTPat (mm256_madd_epi16 lhs rhs)] = admit ()

#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
let lemma_mm256_set1_epi32 (constant: i32)
  : Lemma (ensures forall (j: nat). j < 8 ==>
             lane32 (mm256_set1_epi32 constant) j == v constant /\
             ((0 <= v constant /\ v constant < pow2 16) ==>
               (get_lane (mm256_set1_epi32 constant) (2 * j) == (cast constant <: i16) /\
                get_lane (mm256_set1_epi32 constant) (2 * j + 1) == mk_i16 0)))
          [SMTPat (mm256_set1_epi32 constant)] =
  reveal_opaque (`%mm256_set1_epi32) mm256_set1_epi32;
  Canon.lemma_mm256_set1_epi32 constant;
  let r = mm256_set1_epi32 constant in
  let aux (j: nat{j < 8})
      : Lemma (lane32 r j == v constant /\
               ((0 <= v constant /\ v constant < pow2 16) ==>
                 (get_lane r (2 * j) == (cast constant <: i16) /\
                  get_lane r (2 * j + 1) == mk_i16 0))) =
    lemma_lane32_eq_to_i32x8 r j;
    Canon.lemma_iv_set1_epi32 constant j;
    assert (lane32 r j == v constant);
    assert_norm (pow2 16 == 65536);
    introduce (0 <= v constant /\ v constant < pow2 16) ==>
              (get_lane r (2 * j) == (cast constant <: i16) /\ get_lane r (2 * j + 1) == mk_i16 0)
    with _pf. (
      lemma_halves r j;
      FStar.Math.Lemmas.small_div (v constant) (pow2 16);
      assert (v (get_lane r (2 * j + 1)) == 0);
      assert (get_lane r (2 * j + 1) == mk_i16 0);
      assert (v (get_lane r (2 * j)) == (v constant) @% pow2 16);
      assert (v (cast constant <: i16) == (v constant) @% pow2 16);
      assert (get_lane r (2 * j) == (cast constant <: i16))
    )
  in
  Classical.forall_intro aux
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
let lemma_mm256_srai_epi32 (v_SHIFT_BY: i32) (vector: t_Vec256)
  : Lemma (ensures
             (v v_SHIFT_BY >= 0 /\ v v_SHIFT_BY < 32) ==>
             (forall (j: nat). j < 8 ==>
                lane32 (mm256_srai_epi32 v_SHIFT_BY vector) j == (lane32 vector j) / pow2 (v v_SHIFT_BY)))
          [SMTPat (mm256_srai_epi32 v_SHIFT_BY vector)] =
  reveal_opaque (`%mm256_srai_epi32) mm256_srai_epi32;
  Canon.lemma_mm256_srai_epi32 v_SHIFT_BY vector;
  let r = mm256_srai_epi32 v_SHIFT_BY vector in
  introduce (v v_SHIFT_BY >= 0 /\ v v_SHIFT_BY < 32) ==>
            (forall (j: nat). j < 8 ==>
               lane32 r j == (lane32 vector j) / pow2 (v v_SHIFT_BY))
  with _pf. (
    let aux (j: nat{j < 8}) : Lemma (lane32 r j == (lane32 vector j) / pow2 (v v_SHIFT_BY)) =
      lemma_lane32_eq_to_i32x8 r j;
      lemma_lane32_eq_to_i32x8 vector j;
      Canon.lemma_iv_srai32 v_SHIFT_BY (Canon.to_i32x8 vector) j
    in
    Classical.forall_intro aux
  )
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"
let lemma_mm256_srli_epi32 (v_SHIFT_BY: i32) (vector: t_Vec256)
  : Lemma (ensures
             (v v_SHIFT_BY > 0 /\ v v_SHIFT_BY < 32) ==>
             (forall (j: nat). j < 8 ==>
                lane32 (mm256_srli_epi32 v_SHIFT_BY vector) j ==
                (lane32 vector j % 4294967296) / pow2 (v v_SHIFT_BY)))
          [SMTPat (mm256_srli_epi32 v_SHIFT_BY vector)] =
  reveal_opaque (`%mm256_srli_epi32) mm256_srli_epi32;
  Canon.lemma_mm256_srli_epi32 v_SHIFT_BY vector;
  let r = mm256_srli_epi32 v_SHIFT_BY vector in
  introduce (v v_SHIFT_BY > 0 /\ v v_SHIFT_BY < 32) ==>
            (forall (j: nat). j < 8 ==>
               lane32 r j == (lane32 vector j % 4294967296) / pow2 (v v_SHIFT_BY))
  with _pf. (
    let aux (j: nat{j < 8})
        : Lemma (lane32 r j == (lane32 vector j % 4294967296) / pow2 (v v_SHIFT_BY)) =
      lemma_lane32_eq_to_i32x8 r j;
      lemma_lane32_eq_to_i32x8 vector j;
      Canon.lemma_iv_srli32 v_SHIFT_BY (Canon.to_i32x8 vector) j;
      let xj = Funarr.impl_5__get (mk_u64 8) #i32 (Canon.to_i32x8 vector) (mk_u64 j) in
      assert_norm (pow2 32 == 4294967296);
      (* cast i32->u32 is the unsigned rep; u32 >>! = floor div; the result is
         < 2^31 (shift>=1) so cast back to i32 is identity. *)
      assert (v (cast xj <: u32) == (v xj) % pow2 32);
      FStar.Math.Lemmas.lemma_div_lt_nat ((v xj) % pow2 32) 32 (v v_SHIFT_BY);
      Spec.Utils.lemma_range_at_percent (((v xj) % pow2 32) / pow2 (v v_SHIFT_BY)) (pow2 32)
    in
    Classical.forall_intro aux
  )
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 400"
let lemma_mm256_slli_epi32 (v_SHIFT_BY: i32) (vector: t_Vec256)
  : Lemma (ensures
             ((v v_SHIFT_BY == 16) ==>
               (forall (k: nat). {:pattern (get_lane (mm256_slli_epi32 v_SHIFT_BY vector) k)}
                  k < 16 ==>
                  get_lane (mm256_slli_epi32 v_SHIFT_BY vector) k ==
                    (if k % 2 = 0 then mk_i16 0 else get_lane vector (k - 1)))) /\
             ((v v_SHIFT_BY >= 0 /\ v v_SHIFT_BY < 32) ==>
               (forall (j: nat). j < 8 ==>
                  lane32 (mm256_slli_epi32 v_SHIFT_BY vector) j ==
                    (lane32 vector j * pow2 (v v_SHIFT_BY)) @% 4294967296)))
          [SMTPat (mm256_slli_epi32 v_SHIFT_BY vector)] =
  reveal_opaque (`%mm256_slli_epi32) mm256_slli_epi32;
  Canon.lemma_mm256_slli_epi32 v_SHIFT_BY vector;
  let r = mm256_slli_epi32 v_SHIFT_BY vector in
  assert_norm (pow2 32 == 4294967296);
  let laneB (j: nat{j < 8})
      : Lemma (requires v v_SHIFT_BY >= 0 /\ v v_SHIFT_BY < 32)
              (ensures lane32 r j == (lane32 vector j * pow2 (v v_SHIFT_BY)) @% 4294967296) =
    lemma_lane32_eq_to_i32x8 r j;
    lemma_lane32_eq_to_i32x8 vector j;
    Canon.lemma_iv_slli32 v_SHIFT_BY (Canon.to_i32x8 vector) j;
    let xj = Funarr.impl_5__get (mk_u64 8) #i32 (Canon.to_i32x8 vector) (mk_u64 j) in
    assert (v (cast xj <: u32) == (v xj) % pow2 32);
    FStar.Math.Lemmas.lemma_mod_mul_distr_l (v xj) (pow2 (v v_SHIFT_BY)) (pow2 32);
    FStar.Math.Lemmas.lemma_mod_mod ((v xj * pow2 (v v_SHIFT_BY)) % pow2 32)
      (v xj * pow2 (v v_SHIFT_BY)) (pow2 32)
  in
  let laneA (j: nat{j < 8})
      : Lemma (requires v v_SHIFT_BY == 16)
              (ensures get_lane r (2 * j) == mk_i16 0 /\
                       get_lane r (2 * j + 1) == get_lane vector (2 * j)) =
    laneB j;
    lemma_halves r j;
    lemma_halves vector j;
    assert_norm (pow2 32 == 4294967296);
    lemma_shl16 (lane32 vector j)
  in
  introduce (v v_SHIFT_BY == 16) ==>
            (forall (k: nat). {:pattern (get_lane r k)} k < 16 ==>
               get_lane r k == (if k % 2 = 0 then mk_i16 0 else get_lane vector (k - 1)))
  with _pf. (
    let auxA (k: nat{k < 16})
        : Lemma (get_lane r k == (if k % 2 = 0 then mk_i16 0 else get_lane vector (k - 1))) =
      laneA (k / 2)
    in
    Classical.forall_intro auxA
  );
  introduce (v v_SHIFT_BY >= 0 /\ v v_SHIFT_BY < 32) ==>
            (forall (j: nat). j < 8 ==>
               lane32 r j == (lane32 vector j * pow2 (v v_SHIFT_BY)) @% 4294967296)
  with _pf. (
    let auxB (j: nat{j < 8})
        : Lemma (lane32 r j == (lane32 vector j * pow2 (v v_SHIFT_BY)) @% 4294967296) = laneB j
    in
    Classical.forall_intro auxB
  )
#pop-options

[@@ "trusted: validated-axiom: lane32 view of mm256_unpacklo_epi32 (core-models differential-tested)"]
let lemma_mm256_unpacklo_epi32 (lhs rhs: t_Vec256)
  : Lemma (ensures forall (j: nat). j < 8 ==>
             lane32 (mm256_unpacklo_epi32 lhs rhs) j ==
             (match j with
               | 0 -> lane32 lhs 0 | 1 -> lane32 rhs 0
               | 2 -> lane32 lhs 1 | 3 -> lane32 rhs 1
               | 4 -> lane32 lhs 4 | 5 -> lane32 rhs 4
               | 6 -> lane32 lhs 5 | _ -> lane32 rhs 5))
          [SMTPat (mm256_unpacklo_epi32 lhs rhs)] = admit ()

[@@ "trusted: validated-axiom: lane32 view of mm256_unpackhi_epi32 (core-models differential-tested)"]
let lemma_mm256_unpackhi_epi32 (lhs rhs: t_Vec256)
  : Lemma (ensures forall (j: nat). j < 8 ==>
             lane32 (mm256_unpackhi_epi32 lhs rhs) j ==
             (match j with
               | 0 -> lane32 lhs 2 | 1 -> lane32 rhs 2
               | 2 -> lane32 lhs 3 | 3 -> lane32 rhs 3
               | 4 -> lane32 lhs 6 | 5 -> lane32 rhs 6
               | 6 -> lane32 lhs 7 | _ -> lane32 rhs 7))
          [SMTPat (mm256_unpackhi_epi32 lhs rhs)] = admit ()

(* lane32-view of the qword permutation (mm256_unpackhi_epi64); sha3's u64x4-view
   of the same op stays in the intrinsics tree.  Called by Compress (mulhi
   composite); also SMTPat. *)
[@@ "trusted: validated-axiom: lane32 view of mm256_unpackhi_epi64 (core-models differential-tested)"]
let lemma_mm256_unpackhi_epi64_lane32 (lhs rhs: t_Vec256)
  : Lemma (ensures forall (j: nat). j < 8 ==>
            lane32 (mm256_unpackhi_epi64 lhs rhs) j ==
            (match j with
              | 0 -> lane32 lhs 2 | 1 -> lane32 lhs 3
              | 2 -> lane32 rhs 2 | 3 -> lane32 rhs 3
              | 4 -> lane32 lhs 6 | 5 -> lane32 lhs 7
              | 6 -> lane32 rhs 6 | _ -> lane32 rhs 7))
          [SMTPat (mm256_unpackhi_epi64 lhs rhs)] = admit ()

(* ── get_lane-permutation facts ───────────────────────────────────────────── *)

[@@ "trusted: validated-axiom: get_lane view of mm256_shuffle_epi32 (core-models differential-tested)"]
let lemma_mm256_shuffle_epi32 (v_CONTROL: i32) (vector: t_Vec256)
  : Lemma (ensures forall (k: nat). {:pattern (get_lane (mm256_shuffle_epi32 v_CONTROL vector) k)}
             k < 16 ==>
             get_lane (mm256_shuffle_epi32 v_CONTROL vector) k ==
               get_lane vector (2 * shuffle32_src v_CONTROL (k / 2) + k % 2))
          [SMTPat (mm256_shuffle_epi32 v_CONTROL vector)] = admit ()

[@@ "trusted: validated-axiom: get_lane view of mm256_permute4x64_epi64 (core-models differential-tested)"]
let lemma_mm256_permute4x64_epi64 (v_CONTROL: i32) (vector: t_Vec256)
  : Lemma (ensures forall (k: nat). {:pattern (get_lane (mm256_permute4x64_epi64 v_CONTROL vector) k)}
             k < 16 ==>
             get_lane (mm256_permute4x64_epi64 v_CONTROL vector) k ==
               get_lane vector (4 * permute64_src v_CONTROL (k / 4) + k % 4))
          [SMTPat (mm256_permute4x64_epi64 v_CONTROL vector)] = admit ()

[@@ "trusted: validated-axiom: get_lane view of mm256_castsi128_si256 (core-models differential-tested)"]
let lemma_mm256_castsi128_si256 (vector: t_Vec128)
  : Lemma (ensures forall (k: nat). {:pattern (get_lane (mm256_castsi128_si256 vector) k)}
             k < 8 ==> get_lane (mm256_castsi128_si256 vector) k == get_lane128 vector k)
          [SMTPat (mm256_castsi128_si256 vector)] = admit ()

[@@ "trusted: validated-axiom: get_lane view of mm256_cvtepi16_epi32 (core-models differential-tested)"]
let lemma_mm256_cvtepi16_epi32 (vector: t_Vec128)
  : Lemma (ensures forall (j: nat). j < 8 ==>
             get_lane (mm256_cvtepi16_epi32 vector) (2 * j) == get_lane128 vector j /\
             get_lane (mm256_cvtepi16_epi32 vector) (2 * j + 1) ==
               (if v (get_lane128 vector j) < 0 then mk_i16 (- 1) else mk_i16 0))
          [SMTPat (mm256_cvtepi16_epi32 vector)] = admit ()

[@@ "trusted: validated-axiom: sat_i16 view of mm256_packs_epi32 (core-models differential-tested)"]
let lemma_mm256_packs_epi32 (lhs rhs: t_Vec256)
  : Lemma (ensures forall (k: nat). k < 16 ==>
             get_lane (mm256_packs_epi32 lhs rhs) k ==
             (if k < 4
               then sat_i16 (lane32 lhs k)
               else
                 if k < 8
                 then sat_i16 (lane32 rhs (k - 4))
                 else if k < 12 then sat_i16 (lane32 lhs (k - 4)) else sat_i16 (lane32 rhs (k - 8))))
          [SMTPat (mm256_packs_epi32 lhs rhs)] = admit ()

[@@ "trusted: validated-axiom: get_lane view of mm256_inserti128_si256 (core-models differential-tested)"]
let lemma_mm256_inserti128_si256 (v_CONTROL: i32) (vector: t_Vec256) (vector_i128: t_Vec128)
  : Lemma (ensures forall (k: nat). {:pattern (get_lane (mm256_inserti128_si256 v_CONTROL vector vector_i128) k)}
             k < 16 ==>
             get_lane (mm256_inserti128_si256 v_CONTROL vector vector_i128) k ==
             (if (v v_CONTROL) % 2 = 1
               then (if k < 8 then get_lane vector k else get_lane128 vector_i128 (k - 8))
               else (if k < 8 then get_lane128 vector_i128 k else get_lane vector k)))
          [SMTPat (mm256_inserti128_si256 v_CONTROL vector vector_i128)] = admit ()

[@@ "trusted: validated-axiom: blend_sel view of mm256_blend_epi16 (core-models differential-tested)"]
let lemma_mm256_blend_epi16 (v_CONTROL: i32) (lhs rhs: t_Vec256)
  : Lemma (ensures forall (k: nat). {:pattern (get_lane (mm256_blend_epi16 v_CONTROL lhs rhs) k)}
             k < 16 ==>
             get_lane (mm256_blend_epi16 v_CONTROL lhs rhs) k ==
               (if blend_sel v_CONTROL k then get_lane rhs k else get_lane lhs k))
          [SMTPat (mm256_blend_epi16 v_CONTROL lhs rhs)] = admit ()

(* ── i16x8-view (128-bit vector) facts ────────────────────────────────────── *)

[@@ "trusted: validated-axiom: i16x8 view of mm_add_epi16 (core-models differential-tested)"]
let lemma_mm_add_epi16 (lhs rhs: t_Vec128)
  : Lemma (vec128_as_i16x8 (mm_add_epi16 lhs rhs)
           == Spec.Utils.map2 ( +. ) (vec128_as_i16x8 lhs) (vec128_as_i16x8 rhs))
          [SMTPat (vec128_as_i16x8 (mm_add_epi16 lhs rhs))] = admit ()

[@@ "trusted: validated-axiom: i16x8 view of mm_sub_epi16 (core-models differential-tested)"]
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_mm_sub_epi16 (lhs rhs: t_Vec128)
  : Lemma (vec128_as_i16x8 (mm_sub_epi16 lhs rhs)
           == Spec.Utils.map2 ( -. ) (vec128_as_i16x8 lhs) (vec128_as_i16x8 rhs))
          [SMTPat (vec128_as_i16x8 (mm_sub_epi16 lhs rhs))] =
  reveal_opaque (`%mm_sub_epi16) mm_sub_epi16;
  Canon.lemma_mm_sub_epi16 lhs rhs;
  Seq.lemma_eq_intro (vec128_as_i16x8 (mm_sub_epi16 lhs rhs))
                     (Spec.Utils.map2 ( -. ) (vec128_as_i16x8 lhs) (vec128_as_i16x8 rhs))
#pop-options

[@@ "trusted: validated-axiom: i16x8 view of mm_mullo_epi16 (core-models differential-tested)"]
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_mm_mullo_epi16 (lhs rhs: t_Vec128)
  : Lemma (vec128_as_i16x8 (mm_mullo_epi16 lhs rhs)
           == Spec.Utils.map2 mul_mod (vec128_as_i16x8 lhs) (vec128_as_i16x8 rhs))
          [SMTPat (vec128_as_i16x8 (mm_mullo_epi16 lhs rhs))] =
  reveal_opaque (`%mm_mullo_epi16) mm_mullo_epi16;
  Canon.lemma_mm_mullo_epi16 lhs rhs;
  Seq.lemma_eq_intro (vec128_as_i16x8 (mm_mullo_epi16 lhs rhs))
                     (Spec.Utils.map2 mul_mod (vec128_as_i16x8 lhs) (vec128_as_i16x8 rhs))
#pop-options

[@@ "trusted: validated-axiom: i16x8 view of mm_mulhi_epi16 (core-models differential-tested)"]
#push-options "--fuel 2 --ifuel 1 --z3rlimit 200"
let lemma_mm_mulhi_epi16 (lhs rhs: t_Vec128)
  : Lemma (vec128_as_i16x8 (mm_mulhi_epi16 lhs rhs)
           == Spec.Utils.map2 (fun x y ->
                cast (((cast x <: i32) *. (cast y <: i32)) >>! (mk_i32 16)) <: i16)
              (vec128_as_i16x8 lhs)
              (vec128_as_i16x8 rhs))
          [SMTPat (vec128_as_i16x8 (mm_mulhi_epi16 lhs rhs))] =
  reveal_opaque (`%mm_mulhi_epi16) mm_mulhi_epi16;
  Canon.lemma_mm_mulhi_epi16 lhs rhs;
  Seq.lemma_eq_intro (vec128_as_i16x8 (mm_mulhi_epi16 lhs rhs))
              (Spec.Utils.map2 (fun x y ->
                cast (((cast x <: i32) *. (cast y <: i32)) >>! (mk_i32 16)) <: i16)
              (vec128_as_i16x8 lhs)
              (vec128_as_i16x8 rhs))
#pop-options

[@@ "trusted: validated-axiom: i16x8 view of mm_set1_epi16 (core-models differential-tested)"]
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let lemma_mm_set1_epi16 (constant: i16)
  : Lemma (vec128_as_i16x8 (mm_set1_epi16 constant) == Spec.Utils.create (sz 8) constant)
          [SMTPat (vec128_as_i16x8 (mm_set1_epi16 constant))] =
  reveal_opaque (`%mm_set1_epi16) mm_set1_epi16;
  Canon.lemma_mm_set1_epi16 constant;
  Seq.lemma_eq_intro (vec128_as_i16x8 (mm_set1_epi16 constant))
                     (Spec.Utils.create (sz 8) constant)
#pop-options

(* ── Bit-function view of a core-models t_BitVec ──────────────────────────────
   core-models `t_BitVec N` is structurally a bit-array (a `t_FunArray` of
   `t_Bit`).  `bv_bit` is its DEFINITIONAL view as a pcm-style bit function
   (`nat -> bit`): it reads bit `i` through the `t_Index` instance and maps
   `t_Bit` to `{0,1}`.  This is a DEFINITION, NOT a trusted axiom — it replaces
   the pcm `bit_vec` FUNCTION application (`v (idx)`) that the deferred bridges
   below used, phrasing them over the real core-models struct instead.  The
   migrated Serialize/Compress/Sampling bit proofs apply the vector via `bv_bit`
   in place of the pcm direct application. *)
let bv_bit (#n: u64) (bv: Libcrux_core_models.Abstractions.Bitvec.t_BitVec n)
           (i: nat{i < v n}) : Rust_primitives.Integers.bit =
  match bv.[ mk_u64 i ] <: Libcrux_core_models.Abstractions.Bit.t_Bit with
  | Libcrux_core_models.Abstractions.Bit.Bit_One  -> 1
  | Libcrux_core_models.Abstractions.Bit.Bit_Zero -> 0

(* Cast / extract preserve the underlying bits — PROVEN from the transparent
   core-models ops (`e_mm256_castsi256_si128 v = from_fn (fun i -> v.[i])`,
   `e_mm256_extracti128_si256 1 v = from_fn (fun i -> v.[i + 128])`).  NOT
   trusted axioms; they discharge the `cast vc k == vc k` step that pcm's
   Compress/Ntt bit proofs relied on. *)
let lemma_bv_bit_castsi256_si128 (vc: t_Vec256) (k: nat{k < 128})
  : Lemma (bv_bit (mm256_castsi256_si128 vc) k == bv_bit vc k)
  = reveal_opaque (`%mm256_castsi256_si128) mm256_castsi256_si128

let lemma_bv_bit_extracti128_si256_1 (vc: t_Vec256) (k: nat{k < 128})
  : Lemma (bv_bit (mm256_extracti128_si256 (mk_i32 1) vc) k == bv_bit vc (k + 128))
  = reveal_opaque (`%mm256_extracti128_si256) mm256_extracti128_si256

(* ── Bit-level lane-view bridges (over core-models `t_BitVec`) ─────────────────
   The i16x16 / i16x8 lane view's `d`-bit-per-element serialization at bit `i`
   equals raw bit `(i/d)*16 + i%d` of the underlying vector.  Trusted axioms
   (verbatim the pcm `Avx2_extract.fsti` facts, RHS re-phrased over the real
   `t_BitVec` via `bv_bit`); validated by the core-models differential tests.
   admit-NEUTRAL: pcm carried these as abstract `val`s. *)
[@@ "trusted: validated-axiom: i16x16 lane-view d-bit serialization equals raw t_BitVec bits (core-models differential-tested)"]
let bit_vec_of_int_t_array_vec256_as_i16x16_lemma
      (vec: t_Vec256) (d: nat{d > 0 /\ d <= 16}) (i: nat{i < 16 * d})
    : Lemma (Rust_primitives.BitVectors.bit_vec_of_int_t_array (vec256_as_i16x16 vec) d i
             == bv_bit vec ((i / d) * 16 + i % d))
  = admit ()

[@@ "trusted: validated-axiom: i16x8 lane-view d-bit serialization equals raw t_BitVec bits (core-models differential-tested)"]
let bit_vec_of_int_t_array_vec128_as_i16x8_lemma
      (vec: t_Vec128) (d: nat{d > 0 /\ d <= 16}) (i: nat{i < 8 * d})
    : Lemma (Rust_primitives.BitVectors.bit_vec_of_int_t_array (vec128_as_i16x8 vec) d i
             == bv_bit vec ((i / d) * 16 + i % d))
  = admit ()

(* ============================================================================
   DEFERRED — bit-level bridges + byte store/load, authored per-module when
   Serialize / Compress / Sampling migrate (they need a `t_BitVec`-struct
   representation adaptation: the pcm form below applies the underlying vector as
   a `bit_vec` FUNCTION (`v (idx)`), invalid over core-models `t_BitVec`; the
   replacement indexes via `t_Index` / `to_vec`).  Preserved verbatim from the
   pcm `Libcrux_intrinsics.Avx2_extract.fsti` (source of truth) so the exact fact
   shapes are recoverable.  Consumers of these (top-`Avx2`, `Serialize`,
   `Sampling`) stay RED until then.

   val bit_vec_of_int_t_array_vec256_as_i16x16_lemma
         (v: bit_vec 256) (d: nat{d > 0 /\ d <= 16}) (i: nat{i < 16 * d})
       : Lemma (Rust_primitives.BitVectors.bit_vec_of_int_t_array
                 (vec256_as_i16x16 v) d i == v ((i / d) * 16 + i % d))

   val bit_vec_of_int_t_array_vec128_as_i16x8_lemma
         (v: bit_vec 128) (d: nat{d > 0 /\ d <= 16}) (i: nat{i < 8 * d})
       : Lemma (Rust_primitives.BitVectors.bit_vec_of_int_t_array
                 (vec128_as_i16x8 v) d i == v ((i / d) * 16 + i % d))

   lemma_mm256_storeu_si256_u8_bit_vec (output: t_Slice u8) (vector: t_Vec256)
     : Lemma (requires Core_models.Slice.impl__len #u8 output == mk_usize 32)
             (ensures (let output_future = mm256_storeu_si256_u8 output vector in
                Core_models.Slice.impl__len #u8 output_future ==
                  Core_models.Slice.impl__len #u8 output /\
                (let output_arr: t_Array u8 (sz 32) = output_future in
                 BitVecEq.bit_vec_equal
                   (Rust_primitives.BitVectors.bit_vec_of_int_t_array output_arr 8) vector)))
       [SMTPat (mm256_storeu_si256_u8 output vector)]

   lemma_mm256_loadu_si256_u8_bit_vec (input: t_Slice u8)
       : Lemma (requires Core_models.Slice.impl__len #u8 input == mk_usize 32)
               (ensures (let input_arr: t_Array u8 (sz 32) = input in
                 BitVecEq.bit_vec_equal (mm256_loadu_si256_u8 input)
                   (Rust_primitives.BitVectors.bit_vec_of_int_t_array input_arr 8)))
       [SMTPat (mm256_loadu_si256_u8 input)]

   mm256_cmpgt_epi16 bit-form: forall (i: nat{i < 256}). result i ==
     (if (vec256_as_i16x16 lhs).[i/16] > (vec256_as_i16x16 rhs).[i/16] then 1 else 0)
   ========================================================================== *)
