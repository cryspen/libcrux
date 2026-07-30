module Libcrux_ml_kem.Vector.Avx2.Byteperm_theory
#set-options "--fuel 0 --ifuel 1 --z3rlimit 50"
open FStar.Mul
open Core_models
open Libcrux_intrinsics.Avx2
open Libcrux_intrinsics.Avx2_ml_kem_views

module Funarr = Libcrux_core_models.Abstractions.Funarr
module Canon  = Libcrux_core_models.Intrinsics_views
module IV     = Libcrux_core_models.Core_arch.X86.Interpretations.Int_vec
module IVi    = Libcrux_core_models.Abstractions.Bitvec.Int_vec_interp

(* ============================================================================
   256-bit BYTE/DWORD PERMUTATION bit semantics — `mm256_shuffle_epi8` (VPSHUFB)
   and `mm256_permutevar8x32_epi32` (VPERMD), in `bv_bit` form.

   These are the two ops the AVX2 serialize widths use to gather the packed
   bytes after `mm256_concat_pairs_n`, and neither had a bit-level fact: the
   companion carries only the 128-bit `lemma_bv_bit_mm_shuffle_epi8`, and the
   canonical `Libcrux_core_models.Intrinsics_views` carries the 256-bit SELECT
   branch (`lemma_iv_shuffle_epi8_sel`) but not the 256-bit ZEROING branch.
   That last one is proven here (mirror of the canonical 128-bit
   `lemma_iv_mm_shuffle_epi8_neg`) — developed in the consumer per
   `feedback_develop_locally_upstream_once`, to be upstreamed to core-models
   once the width sweep has exercised it.

   Own module, not appended to `Libcrux_intrinsics.Avx2_ml_kem_views`, for the
   reason item 1 of this session measured: a 2000-line host costs these proofs
   an order of magnitude, and iterating on them there costs ~18 min a cycle.

   SELECT INDEX AS A FREE PARAMETER.  Both lemmas take the resolved source
   index (`sel`) as a parameter constrained in the `requires`, rather than
   recomputing it in the `ensures`.  Callers pass ground masks
   (`mm256_set_epi8 …`/`mm256_set_epi32 …`), so `sel` is a literal at the call
   site and the index algebra never enters the consumer's context — the
   ground-literal discipline of skill §7. *)

(* Byte / dword of a 256-bit vector, in the canonical FunArray view. Plain
   (transparent) definitions: they must stay delta-equal to what the canonical
   op lemmas produce. *)
let vec256_byte (bv: t_Vec256) (k: nat{k < 32}) : i8 =
  Funarr.impl_5__get (mk_u64 32) #i8 (Canon.to_i8x32 bv) (mk_u64 k)

let vec256_dword (bv: t_Vec256) (j: nat{j < 8}) : i32 =
  Funarr.impl_5__get (mk_u64 8) #i32 (Canon.to_i32x8 bv) (mk_u64 j)

(* ── VPSHUFB, zeroing branch, at the Int_vec layer ────────────────────────────
   The 256-bit twin of the canonical `lemma_iv_mm_shuffle_epi8_neg`: a negative
   index byte has its high bit set once wrapped to u8, so the op takes the
   zeroing branch. *)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 300"
let lemma_iv256_shuffle_epi8_neg (a b: Funarr.t_FunArray (mk_u64 32) i8) (i: nat{i < 32})
  : Lemma (requires v (Funarr.impl_5__get (mk_u64 32) #i8 b (mk_u64 i)) < 0)
          (ensures Funarr.impl_5__get (mk_u64 32) #i8 (IV.e_mm256_shuffle_epi8 a b) (mk_u64 i) ==
                   mk_i8 0) =
  let bi = Funarr.impl_5__get (mk_u64 32) #i8 b (mk_u64 i) in
  let idx: u8 = cast bi <: u8 in
  assert (v idx >= 128);
  Canon.lemma_u8_high_bit_set idx;
  assert (Funarr.impl_5__get (mk_u64 32) #i8 (IV.e_mm256_shuffle_epi8 a b) (mk_u64 i) == mk_i8 0)
    by (FStar.Tactics.norm [delta_only [`%Libcrux_core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_shuffle_epi8];
                            iota; zeta; primops];
        FStar.Tactics.smt ())
#pop-options

(* ── VPSHUFB, select branch, in bv_bit form ───────────────────────────────── *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"
let lemma_bv_bit_mm256_shuffle_epi8_sel (a b: t_Vec256) (i: nat{i < 256}) (sel: nat{sel < 32})
  : Lemma (requires v (vec256_byte b (i / 8)) >= 0 /\
                    sel == 16 * ((i / 8) / 16) + (v (vec256_byte b (i / 8))) % 16)
          (ensures bv_bit (mm256_shuffle_epi8 a b) i == bv_bit a (8 * sel + i % 8)) =
  reveal_opaque (`%mm256_shuffle_epi8) mm256_shuffle_epi8;
  Canon.lemma_mm256_shuffle_epi8 a b;
  let nth = i / 8 in
  let sb = i % 8 in
  FStar.Math.Lemmas.euclidean_division_definition i 8;
  let r = mm256_shuffle_epi8 a b in
  Canon.lemma_iv_shuffle_epi8_sel (Canon.to_i8x32 a) (Canon.to_i8x32 b) nth;
  Canon.lemma_readback Rust_primitives.Integers.I8 (mk_u64 256) (mk_u64 32) r (mk_u64 nth) sb;
  lemma_bv_bit_reader 8 r nth sb;
  Canon.lemma_readback Rust_primitives.Integers.I8 (mk_u64 256) (mk_u64 32) a (mk_u64 sel) sb;
  lemma_bv_bit_reader 8 a sel sb
#pop-options

(* ── VPSHUFB, zeroing branch, in bv_bit form ──────────────────────────────── *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"
let lemma_bv_bit_mm256_shuffle_epi8_neg (a b: t_Vec256) (i: nat{i < 256})
  : Lemma (requires v (vec256_byte b (i / 8)) < 0)
          (ensures bv_bit (mm256_shuffle_epi8 a b) i == 0) =
  reveal_opaque (`%mm256_shuffle_epi8) mm256_shuffle_epi8;
  Canon.lemma_mm256_shuffle_epi8 a b;
  let nth = i / 8 in
  let sb = i % 8 in
  FStar.Math.Lemmas.euclidean_division_definition i 8;
  let r = mm256_shuffle_epi8 a b in
  lemma_iv256_shuffle_epi8_neg (Canon.to_i8x32 a) (Canon.to_i8x32 b) nth;
  Canon.lemma_readback Rust_primitives.Integers.I8 (mk_u64 256) (mk_u64 32) r (mk_u64 nth) sb;
  lemma_bv_bit_reader 8 r nth sb;
  reveal_opaque (`%Rust_primitives.Integers.get_bit)
                (Rust_primitives.Integers.get_bit #Rust_primitives.Integers.I8)
#pop-options

(* ── VPERMD, in bv_bit form ───────────────────────────────────────────────── *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"
let lemma_bv_bit_mm256_permutevar8x32 (a b: t_Vec256) (i: nat{i < 256}) (sel: nat{sel < 8})
  : Lemma (requires v (vec256_dword b (i / 32)) >= 0 /\
                    sel == (v (vec256_dword b (i / 32))) % 8)
          (ensures bv_bit (mm256_permutevar8x32_epi32 a b) i == bv_bit a (32 * sel + i % 32)) =
  reveal_opaque (`%mm256_permutevar8x32_epi32) mm256_permutevar8x32_epi32;
  Canon.lemma_mm256_permutevar8x32_epi32 a b;
  let j = i / 32 in
  let sb = i % 32 in
  FStar.Math.Lemmas.euclidean_division_definition i 32;
  let r = mm256_permutevar8x32_epi32 a b in
  Canon.lemma_iv_permutevar8x32 (Canon.to_i32x8 a) (Canon.to_i32x8 b) j;
  assert ((cast (vec256_dword b j) <: u64) %! mk_u64 8 == mk_u64 sel);
  Canon.lemma_readback Rust_primitives.Integers.I32 (mk_u64 256) (mk_u64 8) r (mk_u64 j) sb;
  lemma_bv_bit_reader 32 r j sb;
  Canon.lemma_readback Rust_primitives.Integers.I32 (mk_u64 256) (mk_u64 8) a (mk_u64 sel) sb;
  lemma_bv_bit_reader 32 a sel sb
#pop-options

(* ============================================================================
   THE serialize_4 GATHER CHAIN

   After `mm256_concat_pairs_n 4`, serialize_4 runs
     shuffle_epi8 <mask>  ->  permutevar8x32 <ctrl>  ->  castsi256_si128
   to collect the 4 low bytes of each 128-bit half into the low 64 bits.
   Stated in two stages, per the session-7 item-1 lesson: stage 1 is the pure
   BIT-VIEW step (ground-dispatched over the 8 live mask bytes), stage 2 is the
   pure INDEX ALGEBRA.  Neither ever runs in the other's context.
   ========================================================================== *)

unfold let ser4_mask =
  mm256_set_epi8 (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
    (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
    (mk_i8 12) (mk_i8 8) (mk_i8 4) (mk_i8 0)
    (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
    (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
    (mk_i8 12) (mk_i8 8) (mk_i8 4) (mk_i8 0)

unfold let ser4_ctrl =
  mm256_set_epi32 (mk_i32 0) (mk_i32 0) (mk_i32 0) (mk_i32 0) (mk_i32 0) (mk_i32 0)
    (mk_i32 4) (mk_i32 0)

(* the 8 LIVE mask bytes (the other 24 are -1 = zeroing, and unreachable here) *)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 300"
let lemma_ser4_mask_bytes (nth: nat{nth < 32})
  : Lemma (requires nth < 4 \/ (nth >= 16 /\ nth < 20))
          (ensures v (vec256_byte ser4_mask nth) == 4 * (nth % 16)) =
  reveal_opaque (`%mm256_set_epi8) mm256_set_epi8;
  Canon.lemma_mm256_set_epi8 (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
    (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
    (mk_i8 12) (mk_i8 8) (mk_i8 4) (mk_i8 0)
    (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
    (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
    (mk_i8 12) (mk_i8 8) (mk_i8 4) (mk_i8 0);
  Canon.lemma_iv_set_epi8 (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
    (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
    (mk_i8 12) (mk_i8 8) (mk_i8 4) (mk_i8 0)
    (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
    (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
    (mk_i8 12) (mk_i8 8) (mk_i8 4) (mk_i8 0) nth
#pop-options

(* the 2 LIVE control dwords *)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 300"
let lemma_ser4_ctrl_dwords (j: nat{j < 2})
  : Lemma (ensures v (vec256_dword ser4_ctrl j) == 4 * j) =
  reveal_opaque (`%mm256_set_epi32) mm256_set_epi32;
  Canon.lemma_mm256_set_epi32 (mk_i32 0) (mk_i32 0) (mk_i32 0) (mk_i32 0) (mk_i32 0) (mk_i32 0)
    (mk_i32 4) (mk_i32 0);
  Canon.lemma_iv_set_epi32 (mk_i32 0) (mk_i32 0) (mk_i32 0) (mk_i32 0) (mk_i32 0) (mk_i32 0)
    (mk_i32 4) (mk_i32 0) j
#pop-options

(* stage 1a — the VPSHUFB step at the 8 live byte positions, ground-dispatched
   on `nth` so the mask byte is a literal in every arm. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 300 --split_queries always"
let lemma_ser4_shuffle_bit (y: t_Vec256) (k: nat{k < 256})
  : Lemma (requires k < 32 \/ (k >= 128 /\ k < 160))
          (ensures bv_bit (mm256_shuffle_epi8 y ser4_mask) k ==
                   bv_bit y (128 * (k / 128) + 32 * ((k / 8) % 16) + k % 8)) =
  let nth = k / 8 in
  let sb = k % 8 in
  FStar.Math.Lemmas.euclidean_division_definition k 8;
  lemma_ser4_mask_bytes nth;
  let sel: nat = 16 * (nth / 16) + (v (vec256_byte ser4_mask nth)) % 16 in
  assert (v (vec256_byte ser4_mask nth) == 4 * (nth % 16));
  assert (nth % 16 < 4);
  FStar.Math.Lemmas.small_mod (4 * (nth % 16)) 16;
  assert (sel == 16 * (nth / 16) + 4 * (nth % 16));
  assert (sel < 32);
  lemma_bv_bit_mm256_shuffle_epi8_sel y ser4_mask k sel;
  assert (8 * sel + sb == 128 * (nth / 16) + 32 * (nth % 16) + sb);
  assert (nth / 16 == k / 128)
#pop-options

(* stage 1b — the VPERMD + cast steps, and the full gather at bit `i < 64`. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 300 --split_queries always"
let lemma_ser4_gather_bit (y: t_Vec256) (i: nat{i < 64})
  : Lemma (ensures
             bv_bit (mm256_castsi256_si128
                       (mm256_permutevar8x32_epi32 (mm256_shuffle_epi8 y ser4_mask) ser4_ctrl)) i ==
             bv_bit y (128 * (i / 32) + 32 * ((i / 8) % 4) + i % 8)) =
  let s = mm256_shuffle_epi8 y ser4_mask in
  let p = mm256_permutevar8x32_epi32 s ser4_ctrl in
  lemma_bv_bit_castsi256_si128 p i;
  let j = i / 32 in
  lemma_ser4_ctrl_dwords j;
  FStar.Math.Lemmas.small_mod (4 * j) 8;
  lemma_bv_bit_mm256_permutevar8x32 s ser4_ctrl i (4 * j);
  let k = 32 * (4 * j) + i % 32 in
  assert (k == 128 * j + i % 32);
  FStar.Math.Lemmas.euclidean_division_definition i 32;
  assert (k < 32 \/ (k >= 128 /\ k < 160));
  lemma_ser4_shuffle_bit y k;
  assert (k / 128 == j);
  assert (k % 8 == i % 8);
  assert ((k / 8) % 16 == (i / 8) % 4)
#pop-options

(* stage 2 — the index algebra: composing the `concat_pairs_n 4` post at the
   gathered index yields exactly `(i/4)*16 + i%4`.  Pure integers, no vectors. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 300 --split_queries always"
let lemma_ser4_index (i: nat{i < 64})
  : Lemma (ensures
             (let g = 128 * (i / 32) + 32 * ((i / 8) % 4) + i % 8 in
              g < 256 /\ g % 32 == i % 8 /\ g / 32 == 4 * (i / 32) + (i / 8) % 4 /\
              (i % 8 < 4 ==> (g / 32) * 32 + g % 32 == (i / 4) * 16 + i % 4) /\
              (i % 8 >= 4 ==> (g / 32) * 32 + 16 + (g % 32 - 4) == (i / 4) * 16 + i % 4))) =
  FStar.Math.Lemmas.euclidean_division_definition i 32;
  FStar.Math.Lemmas.euclidean_division_definition i 8;
  FStar.Math.Lemmas.euclidean_division_definition i 4;
  assert (i / 8 == 4 * (i / 32) + (i / 8) % 4);
  assert (i == 32 * (i / 32) + 8 * ((i / 8) % 4) + i % 8)
#pop-options

(* THE serialize_4 obligation, per output bit.  `y` is the `concat_pairs_n 4`
   result, threaded as a FREE parameter with its bit post as a hypothesis, so
   the caller links by congruence and this module never mentions Serialize. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 300 --split_queries always"
let lemma_serialize_4_gather_bits (x y: t_Vec256) (i: nat{i < 64})
  : Lemma
      (requires (forall (k: nat{k < 256}).
                   bv_bit y k ==
                   (if k % 32 < 4 then bv_bit x ((k / 32) * 32 + k % 32)
                    else if k % 32 < 8 then bv_bit x ((k / 32) * 32 + 16 + (k % 32 - 4))
                    else 0)))
      (ensures bv_bit (mm256_castsi256_si128
                         (mm256_permutevar8x32_epi32 (mm256_shuffle_epi8 y ser4_mask) ser4_ctrl)) i ==
               bv_bit x ((i / 4) * 16 + i % 4)) =
  lemma_ser4_gather_bit y i;
  lemma_ser4_index i
#pop-options
