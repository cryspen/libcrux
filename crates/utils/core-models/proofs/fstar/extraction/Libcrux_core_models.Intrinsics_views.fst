module Libcrux_core_models.Intrinsics_views
#set-options "--fuel 0 --ifuel 1 --z3rlimit 30"
open FStar.Mul
open Core_models

(* ============================================================================
   CANONICAL intrinsics lane-view + op-lemma companion (Option B, Phase 1).

   Single source of truth for the SIMD lane view + the proven op-lemma set that
   ml-kem / ml-dsa / sha3 will (eventually) all `open` — replacing ml-dsa's
   `Spec.Intrinsics`, ml-kem's `Libcrux_intrinsics.Avx2_ml_kem_views`, and sha3's
   companion.  It rests entirely on the differentially-tested `core-models` model.

   The lane VIEW is the CONCRETE core-models conversion `to_iWxL`
   (`Int_vec_interp.e_ee_N__impl__to_*`, a `FunArray`) — re-exported here, NO new
   axiom.  Each op-lemma
     `to_OUT (Avx2.e_mm256_OP a b) == Int_vec.e_mm256_OP (to_IN a) (to_IN b)`
   is PROVEN by a uniform, op-agnostic reduction:
       lift lemma  (Int_vec.Lemmas, differentially-tested `assume val`, [@@ v_LIFT_LEMMA])
     + round-trip  (Int_vec_interp.lemma_conv_rt, PROVEN)
     + Int_vec def (definitional).
   `op_lemma_from_lift_{bin,un}` capture the reduction; each op-lemma is one
   instance (const-generic ops partially-apply the immediate; ternary / two-view /
   scalar-result / raw-passthrough / set ops inline the same two-step body).

   NOTE (SMTPat): op-lemmas are exposed WITHOUT SMTPat — this foundational module
   stays cascade-free; consumers call them explicitly (or a later phase adds
   scoped SMTPats).  Ground-term ops (setzero/…) would otherwise mint variable-
   free triggers (Error 276), see ml-kem `Avx2_ml_kem_views` note.
   ============================================================================ *)

module BV     = Libcrux_core_models.Abstractions.Bitvec
module Funarr = Libcrux_core_models.Abstractions.Funarr
module Bit    = Libcrux_core_models.Abstractions.Bit
module Int    = Rust_primitives.Integers
module IV     = Libcrux_core_models.Core_arch.X86.Interpretations.Int_vec
module IVL    = Libcrux_core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas
module IVi    = Libcrux_core_models.Abstractions.Bitvec.Int_vec_interp
module Avx    = Libcrux_core_models.Core_arch.X86.Avx
module Avx2   = Libcrux_core_models.Core_arch.X86.Avx2
module Sse2   = Libcrux_core_models.Core_arch.X86.Sse2
module Ssse3  = Libcrux_core_models.Core_arch.X86.Ssse3

(* ── bit-vector widths ─────────────────────────────────────────────────────── *)
let bv256 = BV.t_BitVec (mk_u64 256)
let bv128 = BV.t_BitVec (mk_u64 128)

(* ── the canonical lane views = core-models `to_iWxL` (re-export, no new axiom) ─ *)
let to_i16x16  = IVi.e_ee_3__impl__to_i16x16
let from_i16x16 = IVi.e_ee_3__impl__from_i16x16
let to_i32x8   = IVi.e_ee_1__impl__to_i32x8
let from_i32x8  = IVi.e_ee_1__impl__from_i32x8
let to_i64x4   = IVi.e_ee_2__impl__to_i64x4
let from_i64x4  = IVi.e_ee_2__impl__from_i64x4
let to_i8x32   = IVi.e_ee_5__impl__to_i8x32
let from_i8x32  = IVi.e_ee_5__impl__from_i8x32
let to_u32x8   = IVi.e_ee_6__impl__to_u32x8
let to_u64x4   = IVi.e_ee_7__impl__to_u64x4
let from_u64x4  = IVi.e_ee_7__impl__from_u64x4
let to_i128x2  = IVi.e_ee_4__impl__to_i128x2
let from_i128x2 = IVi.e_ee_4__impl__from_i128x2
let to_i128x1  = IVi.e_ee_13__impl__to_i128x1
let to_i32x4   = IVi.e_ee_10__impl__to_i32x4
let from_i32x4  = IVi.e_ee_10__impl__from_i32x4
let to_i64x2   = IVi.e_ee_11__impl__to_i64x2
let from_i64x2  = IVi.e_ee_11__impl__from_i64x2
let to_i16x8   = IVi.e_ee_12__impl__to_i16x8
let from_i16x8  = IVi.e_ee_12__impl__from_i16x8
let to_i8x16   = IVi.e_ee_14__impl__to_i8x16
let from_i8x16  = IVi.e_ee_14__impl__from_i8x16

(* ── the op-agnostic reduction combinators ─────────────────────────────────── *)

(* Every view-output op-lemma reduces to lift + round-trip; general binary form
   (input and output views may differ, e.g. mul_epi32: i32x8 -> i64x4). *)
let op_lemma_from_lift_bin
    (#in_w #out_w: u64)
    (#in_fa #out_fa: Type0)
    (to_in:    BV.t_BitVec in_w  -> in_fa)
    (from_out: out_fa -> BV.t_BitVec out_w)
    (to_out:   BV.t_BitVec out_w -> out_fa)
    (op_bit: BV.t_BitVec in_w -> BV.t_BitVec in_w -> BV.t_BitVec out_w)
    (op_int: in_fa -> in_fa -> out_fa)
    (lift: (a: BV.t_BitVec in_w) -> (b: BV.t_BitVec in_w)
           -> Lemma (op_bit a b == from_out (op_int (to_in a) (to_in b))))
    (rt: (y: out_fa) -> Lemma (to_out (from_out y) == y))
    (a b: BV.t_BitVec in_w)
  : Lemma (to_out (op_bit a b) == op_int (to_in a) (to_in b)) =
  lift a b;
  rt (op_int (to_in a) (to_in b))

(* Unary form (covers `castsi`/`cvtepi`/`abs` and every const-generic op once its
   immediate is partially applied). *)
let op_lemma_from_lift_un
    (#in_w #out_w: u64)
    (#in_fa #out_fa: Type0)
    (to_in:    BV.t_BitVec in_w  -> in_fa)
    (from_out: out_fa -> BV.t_BitVec out_w)
    (to_out:   BV.t_BitVec out_w -> out_fa)
    (op_bit: BV.t_BitVec in_w -> BV.t_BitVec out_w)
    (op_int: in_fa -> out_fa)
    (lift: (x: BV.t_BitVec in_w)
           -> Lemma (op_bit x == from_out (op_int (to_in x))))
    (rt: (y: out_fa) -> Lemma (to_out (from_out y) == y))
    (x: BV.t_BitVec in_w)
  : Lemma (to_out (op_bit x) == op_int (to_in x)) =
  lift x;
  rt (op_int (to_in x))

(* ── per-width round-trips (all instances of the PROVEN generic `lemma_conv_rt`) ─ *)
let rt_i16x16 (y: Funarr.t_FunArray (mk_u64 16) i16) : Lemma (to_i16x16 (from_i16x16 y) == y) =
  IVi.lemma_conv_rt Int.I16 (mk_u64 256) (mk_u64 16) y
let rt_i32x8 (y: Funarr.t_FunArray (mk_u64 8) i32) : Lemma (to_i32x8 (from_i32x8 y) == y) =
  IVi.lemma_conv_rt Int.I32 (mk_u64 256) (mk_u64 8) y
let rt_i64x4 (y: Funarr.t_FunArray (mk_u64 4) i64) : Lemma (to_i64x4 (from_i64x4 y) == y) =
  IVi.lemma_conv_rt Int.I64 (mk_u64 256) (mk_u64 4) y
let rt_u64x4 (y: Funarr.t_FunArray (mk_u64 4) u64) : Lemma (to_u64x4 (from_u64x4 y) == y) =
  IVi.lemma_conv_rt Int.U64 (mk_u64 256) (mk_u64 4) y
let rt_i8x32 (y: Funarr.t_FunArray (mk_u64 32) i8) : Lemma (to_i8x32 (from_i8x32 y) == y) =
  IVi.lemma_conv_rt Int.I8 (mk_u64 256) (mk_u64 32) y
let rt_i128x2 (y: Funarr.t_FunArray (mk_u64 2) i128) : Lemma (to_i128x2 (from_i128x2 y) == y) =
  IVi.lemma_conv_rt Int.I128 (mk_u64 256) (mk_u64 2) y
let rt_i32x4 (y: Funarr.t_FunArray (mk_u64 4) i32) : Lemma (to_i32x4 (from_i32x4 y) == y) =
  IVi.lemma_conv_rt Int.I32 (mk_u64 128) (mk_u64 4) y
let rt_i64x2 (y: Funarr.t_FunArray (mk_u64 2) i64) : Lemma (to_i64x2 (from_i64x2 y) == y) =
  IVi.lemma_conv_rt Int.I64 (mk_u64 128) (mk_u64 2) y
let rt_i16x8 (y: Funarr.t_FunArray (mk_u64 8) i16) : Lemma (to_i16x8 (from_i16x8 y) == y) =
  IVi.lemma_conv_rt Int.I16 (mk_u64 128) (mk_u64 8) y
let rt_i8x16 (y: Funarr.t_FunArray (mk_u64 16) i8) : Lemma (to_i8x16 (from_i8x16 y) == y) =
  IVi.lemma_conv_rt Int.I8 (mk_u64 128) (mk_u64 16) y

(* ============================================================================
   PROVEN op-lemmas — full op set (each an instance of the reduction above).
   ============================================================================ *)

let lemma_mm256_set1_epi32 (x: i32)
  : Lemma (to_i32x8 (Avx.e_mm256_set1_epi32 x) == IV.e_mm256_set1_epi32 x) =
  IVL.e_mm256_set1_epi32' x;
  rt_i32x8 (IV.e_mm256_set1_epi32 x)

let lemma_mm256_mul_epi32 (x: bv256) (y: bv256)
  : Lemma (to_i64x4 (Avx2.e_mm256_mul_epi32 x y) == IV.e_mm256_mul_epi32 (to_i32x8 x) (to_i32x8 y)) =
  op_lemma_from_lift_bin to_i32x8 from_i64x4 to_i64x4
    Avx2.e_mm256_mul_epi32 IV.e_mm256_mul_epi32 IVL.e_mm256_mul_epi32' rt_i64x4 x y

let lemma_mm256_sub_epi32 (x: bv256) (y: bv256)
  : Lemma (to_i32x8 (Avx2.e_mm256_sub_epi32 x y) == IV.e_mm256_sub_epi32 (to_i32x8 x) (to_i32x8 y)) =
  op_lemma_from_lift_bin to_i32x8 from_i32x8 to_i32x8
    Avx2.e_mm256_sub_epi32 IV.e_mm256_sub_epi32 IVL.e_mm256_sub_epi32' rt_i32x8 x y

let lemma_mm256_shuffle_epi32 (v_CONTROL: i32) (x: bv256)
  : Lemma (to_i32x8 (Avx2.e_mm256_shuffle_epi32 v_CONTROL x) == IV.e_mm256_shuffle_epi32 v_CONTROL (to_i32x8 x)) =
  op_lemma_from_lift_un to_i32x8 from_i32x8 to_i32x8
    (Avx2.e_mm256_shuffle_epi32 v_CONTROL) (IV.e_mm256_shuffle_epi32 v_CONTROL) (IVL.e_mm256_shuffle_epi32' v_CONTROL) rt_i32x8 x

let lemma_mm256_blend_epi32 (v_CONTROL: i32) (x: bv256) (y: bv256)
  : Lemma (to_i32x8 (Avx2.e_mm256_blend_epi32 v_CONTROL x y) == IV.e_mm256_blend_epi32 v_CONTROL (to_i32x8 x) (to_i32x8 y)) =
  op_lemma_from_lift_bin to_i32x8 from_i32x8 to_i32x8
    (Avx2.e_mm256_blend_epi32 v_CONTROL) (IV.e_mm256_blend_epi32 v_CONTROL) (IVL.e_mm256_blend_epi32' v_CONTROL) rt_i32x8 x y

let lemma_mm256_set1_epi16 (x: i16)
  : Lemma (to_i16x16 (Avx.e_mm256_set1_epi16 x) == IV.e_mm256_set1_epi16 x) =
  IVL.e_mm256_set1_epi16' x;
  rt_i16x16 (IV.e_mm256_set1_epi16 x)

let lemma_mm_set1_epi16 (x: i16)
  : Lemma (to_i16x8 (Sse2.e_mm_set1_epi16 x) == IV.e_mm_set1_epi16 x) =
  IVL.e_mm_set1_epi16' x;
  rt_i16x8 (IV.e_mm_set1_epi16 x)

let lemma_mm_set_epi32 (e3: i32) (e2: i32) (e1: i32) (e0: i32)
  : Lemma (to_i32x4 (Sse2.e_mm_set_epi32 e3 e2 e1 e0) == IV.e_mm_set_epi32 e3 e2 e1 e0) =
  IVL.e_mm_set_epi32' e3 e2 e1 e0;
  rt_i32x4 (IV.e_mm_set_epi32 e3 e2 e1 e0)

let lemma_mm_add_epi16 (a: bv128) (b: bv128)
  : Lemma (to_i16x8 (Sse2.e_mm_add_epi16 a b) == IV.e_mm_add_epi16 (to_i16x8 a) (to_i16x8 b)) =
  op_lemma_from_lift_bin to_i16x8 from_i16x8 to_i16x8
    Sse2.e_mm_add_epi16 IV.e_mm_add_epi16 IVL.e_mm_add_epi16' rt_i16x8 a b

let lemma_mm256_add_epi16 (a: bv256) (b: bv256)
  : Lemma (to_i16x16 (Avx2.e_mm256_add_epi16 a b) == IV.e_mm256_add_epi16 (to_i16x16 a) (to_i16x16 b)) =
  op_lemma_from_lift_bin to_i16x16 from_i16x16 to_i16x16
    Avx2.e_mm256_add_epi16 IV.e_mm256_add_epi16 IVL.e_mm256_add_epi16' rt_i16x16 a b

let lemma_mm256_add_epi32 (a: bv256) (b: bv256)
  : Lemma (to_i32x8 (Avx2.e_mm256_add_epi32 a b) == IV.e_mm256_add_epi32 (to_i32x8 a) (to_i32x8 b)) =
  op_lemma_from_lift_bin to_i32x8 from_i32x8 to_i32x8
    Avx2.e_mm256_add_epi32 IV.e_mm256_add_epi32 IVL.e_mm256_add_epi32' rt_i32x8 a b

let lemma_mm256_add_epi64 (a: bv256) (b: bv256)
  : Lemma (to_i64x4 (Avx2.e_mm256_add_epi64 a b) == IV.e_mm256_add_epi64 (to_i64x4 a) (to_i64x4 b)) =
  op_lemma_from_lift_bin to_i64x4 from_i64x4 to_i64x4
    Avx2.e_mm256_add_epi64 IV.e_mm256_add_epi64 IVL.e_mm256_add_epi64' rt_i64x4 a b

let lemma_mm256_abs_epi32 (a: bv256)
  : Lemma (to_i32x8 (Avx2.e_mm256_abs_epi32 a) == IV.e_mm256_abs_epi32 (to_i32x8 a)) =
  op_lemma_from_lift_un to_i32x8 from_i32x8 to_i32x8
    Avx2.e_mm256_abs_epi32 IV.e_mm256_abs_epi32 IVL.e_mm256_abs_epi32' rt_i32x8 a

let lemma_mm256_sub_epi16 (a: bv256) (b: bv256)
  : Lemma (to_i16x16 (Avx2.e_mm256_sub_epi16 a b) == IV.e_mm256_sub_epi16 (to_i16x16 a) (to_i16x16 b)) =
  op_lemma_from_lift_bin to_i16x16 from_i16x16 to_i16x16
    Avx2.e_mm256_sub_epi16 IV.e_mm256_sub_epi16 IVL.e_mm256_sub_epi16' rt_i16x16 a b

let lemma_mm_mullo_epi16 (a: bv128) (b: bv128)
  : Lemma (to_i16x8 (Sse2.e_mm_mullo_epi16 a b) == IV.e_mm_mullo_epi16 (to_i16x8 a) (to_i16x8 b)) =
  op_lemma_from_lift_bin to_i16x8 from_i16x8 to_i16x8
    Sse2.e_mm_mullo_epi16 IV.e_mm_mullo_epi16 IVL.e_mm_mullo_epi16' rt_i16x8 a b

let lemma_mm256_cmpgt_epi16 (a: bv256) (b: bv256)
  : Lemma (to_i16x16 (Avx2.e_mm256_cmpgt_epi16 a b) == IV.e_mm256_cmpgt_epi16 (to_i16x16 a) (to_i16x16 b)) =
  op_lemma_from_lift_bin to_i16x16 from_i16x16 to_i16x16
    Avx2.e_mm256_cmpgt_epi16 IV.e_mm256_cmpgt_epi16 IVL.e_mm256_cmpgt_epi16' rt_i16x16 a b

let lemma_mm256_cmpgt_epi32 (a: bv256) (b: bv256)
  : Lemma (to_i32x8 (Avx2.e_mm256_cmpgt_epi32 a b) == IV.e_mm256_cmpgt_epi32 (to_i32x8 a) (to_i32x8 b)) =
  op_lemma_from_lift_bin to_i32x8 from_i32x8 to_i32x8
    Avx2.e_mm256_cmpgt_epi32 IV.e_mm256_cmpgt_epi32 IVL.e_mm256_cmpgt_epi32' rt_i32x8 a b

let lemma_mm256_sign_epi32 (a: bv256) (b: bv256)
  : Lemma (to_i32x8 (Avx2.e_mm256_sign_epi32 a b) == IV.e_mm256_sign_epi32 (to_i32x8 a) (to_i32x8 b)) =
  op_lemma_from_lift_bin to_i32x8 from_i32x8 to_i32x8
    Avx2.e_mm256_sign_epi32 IV.e_mm256_sign_epi32 IVL.e_mm256_sign_epi32' rt_i32x8 a b

let lemma_mm256_movemask_ps (a: bv256)
  : Lemma (Avx.e_mm256_movemask_ps a == IV.e_mm256_movemask_ps (to_i32x8 a)) =
  IVL.e_mm256_movemask_ps' a

let lemma_mm_mulhi_epi16 (a: bv128) (b: bv128)
  : Lemma (to_i16x8 (Sse2.e_mm_mulhi_epi16 a b) == IV.e_mm_mulhi_epi16 (to_i16x8 a) (to_i16x8 b)) =
  op_lemma_from_lift_bin to_i16x8 from_i16x8 to_i16x8
    Sse2.e_mm_mulhi_epi16 IV.e_mm_mulhi_epi16 IVL.e_mm_mulhi_epi16' rt_i16x8 a b

let lemma_mm256_mullo_epi32 (a: bv256) (b: bv256)
  : Lemma (to_i32x8 (Avx2.e_mm256_mullo_epi32 a b) == IV.e_mm256_mullo_epi32 (to_i32x8 a) (to_i32x8 b)) =
  op_lemma_from_lift_bin to_i32x8 from_i32x8 to_i32x8
    Avx2.e_mm256_mullo_epi32 IV.e_mm256_mullo_epi32 IVL.e_mm256_mullo_epi32' rt_i32x8 a b

let lemma_mm256_mulhi_epi16 (a: bv256) (b: bv256)
  : Lemma (to_i16x16 (Avx2.e_mm256_mulhi_epi16 a b) == IV.e_mm256_mulhi_epi16 (to_i16x16 a) (to_i16x16 b)) =
  op_lemma_from_lift_bin to_i16x16 from_i16x16 to_i16x16
    Avx2.e_mm256_mulhi_epi16 IV.e_mm256_mulhi_epi16 IVL.e_mm256_mulhi_epi16' rt_i16x16 a b

let lemma_mm256_mul_epu32 (a: bv256) (b: bv256)
  : Lemma (to_u64x4 (Avx2.e_mm256_mul_epu32 a b) == IV.e_mm256_mul_epu32 (to_u32x8 a) (to_u32x8 b)) =
  op_lemma_from_lift_bin to_u32x8 from_u64x4 to_u64x4
    Avx2.e_mm256_mul_epu32 IV.e_mm256_mul_epu32 IVL.e_mm256_mul_epu32' rt_u64x4 a b

let lemma_mm256_srai_epi16 (v_IMM8: i32) (a: bv256)
  : Lemma (to_i16x16 (Avx2.e_mm256_srai_epi16 v_IMM8 a) == IV.e_mm256_srai_epi16 v_IMM8 (to_i16x16 a)) =
  op_lemma_from_lift_un to_i16x16 from_i16x16 to_i16x16
    (Avx2.e_mm256_srai_epi16 v_IMM8) (IV.e_mm256_srai_epi16 v_IMM8) (IVL.e_mm256_srai_epi16' v_IMM8) rt_i16x16 a

let lemma_mm256_srai_epi32 (v_IMM8: i32) (a: bv256)
  : Lemma (to_i32x8 (Avx2.e_mm256_srai_epi32 v_IMM8 a) == IV.e_mm256_srai_epi32 v_IMM8 (to_i32x8 a)) =
  op_lemma_from_lift_un to_i32x8 from_i32x8 to_i32x8
    (Avx2.e_mm256_srai_epi32 v_IMM8) (IV.e_mm256_srai_epi32 v_IMM8) (IVL.e_mm256_srai_epi32' v_IMM8) rt_i32x8 a

let lemma_mm256_srli_epi16 (v_IMM8: i32) (a: bv256)
  : Lemma (to_i16x16 (Avx2.e_mm256_srli_epi16 v_IMM8 a) == IV.e_mm256_srli_epi16 v_IMM8 (to_i16x16 a)) =
  op_lemma_from_lift_un to_i16x16 from_i16x16 to_i16x16
    (Avx2.e_mm256_srli_epi16 v_IMM8) (IV.e_mm256_srli_epi16 v_IMM8) (IVL.e_mm256_srli_epi16' v_IMM8) rt_i16x16 a

let lemma_mm256_srli_epi32 (v_IMM8: i32) (a: bv256)
  : Lemma (to_i32x8 (Avx2.e_mm256_srli_epi32 v_IMM8 a) == IV.e_mm256_srli_epi32 v_IMM8 (to_i32x8 a)) =
  op_lemma_from_lift_un to_i32x8 from_i32x8 to_i32x8
    (Avx2.e_mm256_srli_epi32 v_IMM8) (IV.e_mm256_srli_epi32 v_IMM8) (IVL.e_mm256_srli_epi32' v_IMM8) rt_i32x8 a

let lemma_mm_srli_epi64 (v_IMM8: i32) (a: bv128)
  : Lemma (to_i64x2 (Sse2.e_mm_srli_epi64 v_IMM8 a) == IV.e_mm_srli_epi64 v_IMM8 (to_i64x2 a)) =
  op_lemma_from_lift_un to_i64x2 from_i64x2 to_i64x2
    (Sse2.e_mm_srli_epi64 v_IMM8) (IV.e_mm_srli_epi64 v_IMM8) (IVL.e_mm_srli_epi64' v_IMM8) rt_i64x2 a

let lemma_mm256_slli_epi32 (v_IMM8: i32) (a: bv256)
  : Lemma (to_i32x8 (Avx2.e_mm256_slli_epi32 v_IMM8 a) == IV.e_mm256_slli_epi32 v_IMM8 (to_i32x8 a)) =
  op_lemma_from_lift_un to_i32x8 from_i32x8 to_i32x8
    (Avx2.e_mm256_slli_epi32 v_IMM8) (IV.e_mm256_slli_epi32 v_IMM8) (IVL.e_mm256_slli_epi32' v_IMM8) rt_i32x8 a

let lemma_mm256_permute4x64_epi64 (v_IMM8: i32) (a: bv256)
  : Lemma (to_i64x4 (Avx2.e_mm256_permute4x64_epi64 v_IMM8 a) == IV.e_mm256_permute4x64_epi64 v_IMM8 (to_i64x4 a)) =
  op_lemma_from_lift_un to_i64x4 from_i64x4 to_i64x4
    (Avx2.e_mm256_permute4x64_epi64 v_IMM8) (IV.e_mm256_permute4x64_epi64 v_IMM8) (IVL.e_mm256_permute4x64_epi64' v_IMM8) rt_i64x4 a

let lemma_mm256_unpackhi_epi64 (a: bv256) (b: bv256)
  : Lemma (to_i64x4 (Avx2.e_mm256_unpackhi_epi64 a b) == IV.e_mm256_unpackhi_epi64 (to_i64x4 a) (to_i64x4 b)) =
  op_lemma_from_lift_bin to_i64x4 from_i64x4 to_i64x4
    Avx2.e_mm256_unpackhi_epi64 IV.e_mm256_unpackhi_epi64 IVL.e_mm256_unpackhi_epi64' rt_i64x4 a b

let lemma_mm256_unpacklo_epi32 (a: bv256) (b: bv256)
  : Lemma (to_i32x8 (Avx2.e_mm256_unpacklo_epi32 a b) == IV.e_mm256_unpacklo_epi32 (to_i32x8 a) (to_i32x8 b)) =
  op_lemma_from_lift_bin to_i32x8 from_i32x8 to_i32x8
    Avx2.e_mm256_unpacklo_epi32 IV.e_mm256_unpacklo_epi32 IVL.e_mm256_unpacklo_epi32' rt_i32x8 a b

let lemma_mm256_unpackhi_epi32 (a: bv256) (b: bv256)
  : Lemma (to_i32x8 (Avx2.e_mm256_unpackhi_epi32 a b) == IV.e_mm256_unpackhi_epi32 (to_i32x8 a) (to_i32x8 b)) =
  op_lemma_from_lift_bin to_i32x8 from_i32x8 to_i32x8
    Avx2.e_mm256_unpackhi_epi32 IV.e_mm256_unpackhi_epi32 IVL.e_mm256_unpackhi_epi32' rt_i32x8 a b

let lemma_mm256_cvtepi16_epi32 (a: bv128)
  : Lemma (to_i32x8 (Avx2.e_mm256_cvtepi16_epi32 a) == IV.e_mm256_cvtepi16_epi32 (to_i16x8 a)) =
  op_lemma_from_lift_un to_i16x8 from_i32x8 to_i32x8
    Avx2.e_mm256_cvtepi16_epi32 IV.e_mm256_cvtepi16_epi32 IVL.e_mm256_cvtepi16_epi32' rt_i32x8 a

let lemma_mm_packs_epi16 (a: bv128) (b: bv128)
  : Lemma (to_i8x16 (Sse2.e_mm_packs_epi16 a b) == IV.e_mm_packs_epi16 (to_i16x8 a) (to_i16x8 b)) =
  op_lemma_from_lift_bin to_i16x8 from_i8x16 to_i8x16
    Sse2.e_mm_packs_epi16 IV.e_mm_packs_epi16 IVL.e_mm_packs_epi16' rt_i8x16 a b

let lemma_mm256_packs_epi32 (a: bv256) (b: bv256)
  : Lemma (to_i16x16 (Avx2.e_mm256_packs_epi32 a b) == IV.e_mm256_packs_epi32 (to_i32x8 a) (to_i32x8 b)) =
  op_lemma_from_lift_bin to_i32x8 from_i16x16 to_i16x16
    Avx2.e_mm256_packs_epi32 IV.e_mm256_packs_epi32 IVL.e_mm256_packs_epi32' rt_i16x16 a b

let lemma_mm256_inserti128_si256 (v_IMM8: i32) (a: bv256) (b: bv128)
  : Lemma (to_i128x2 (Avx2.e_mm256_inserti128_si256 v_IMM8 a b) == IV.e_mm256_inserti128_si256 v_IMM8 (to_i128x2 a) (to_i128x1 b)) =
  IVL.e_mm256_inserti128_si256' v_IMM8 a b;
  rt_i128x2 (IV.e_mm256_inserti128_si256 v_IMM8 (to_i128x2 a) (to_i128x1 b))

let lemma_mm256_blend_epi16 (v_IMM8: i32) (a: bv256) (b: bv256)
  : Lemma (to_i16x16 (Avx2.e_mm256_blend_epi16 v_IMM8 a b) == IV.e_mm256_blend_epi16 v_IMM8 (to_i16x16 a) (to_i16x16 b)) =
  op_lemma_from_lift_bin to_i16x16 from_i16x16 to_i16x16
    (Avx2.e_mm256_blend_epi16 v_IMM8) (IV.e_mm256_blend_epi16 v_IMM8) (IVL.e_mm256_blend_epi16' v_IMM8) rt_i16x16 a b

let lemma_mm256_blendv_ps (a: bv256) (b: bv256) (c: bv256)
  : Lemma (to_i32x8 (Avx.e_mm256_blendv_ps a b c) == IV.e_mm256_blendv_ps (to_i32x8 a) (to_i32x8 b) (to_i32x8 c)) =
  IVL.e_mm256_blendv_ps' a b c;
  rt_i32x8 (IV.e_mm256_blendv_ps (to_i32x8 a) (to_i32x8 b) (to_i32x8 c))

let lemma_mm_movemask_epi8 (a: bv128)
  : Lemma (Sse2.e_mm_movemask_epi8 a == IV.e_mm_movemask_epi8 (to_i8x16 a)) =
  IVL.e_mm_movemask_epi8' a

let lemma_mm256_srlv_epi64 (a: bv256) (b: bv256)
  : Lemma (to_i64x4 (Avx2.e_mm256_srlv_epi64 a b) == IV.e_mm256_srlv_epi64 (to_i64x4 a) (to_i64x4 b)) =
  op_lemma_from_lift_bin to_i64x4 from_i64x4 to_i64x4
    Avx2.e_mm256_srlv_epi64 IV.e_mm256_srlv_epi64 IVL.e_mm256_srlv_epi64' rt_i64x4 a b

let lemma_mm_sllv_epi32 (a: bv128) (b: bv128)
  : Lemma (to_i32x4 (Avx2.e_mm_sllv_epi32 a b) == IV.e_mm_sllv_epi32 (to_i32x4 a) (to_i32x4 b)) =
  op_lemma_from_lift_bin to_i32x4 from_i32x4 to_i32x4
    Avx2.e_mm_sllv_epi32 IV.e_mm_sllv_epi32 IVL.e_mm_sllv_epi32' rt_i32x4 a b

let lemma_mm256_slli_epi64 (v_IMM8: i32) (a: bv256)
  : Lemma (to_i64x4 (Avx2.e_mm256_slli_epi64 v_IMM8 a) == IV.e_mm256_slli_epi64 v_IMM8 (to_i64x4 a)) =
  op_lemma_from_lift_un to_i64x4 from_i64x4 to_i64x4
    (Avx2.e_mm256_slli_epi64 v_IMM8) (IV.e_mm256_slli_epi64 v_IMM8) (IVL.e_mm256_slli_epi64' v_IMM8) rt_i64x4 a

let lemma_mm256_bsrli_epi128 (v_IMM8: i32) (a: bv256)
  : Lemma (to_i128x2 (Avx2.e_mm256_bsrli_epi128 v_IMM8 a) == IV.e_mm256_bsrli_epi128 v_IMM8 (to_i128x2 a)) =
  op_lemma_from_lift_un to_i128x2 from_i128x2 to_i128x2
    (Avx2.e_mm256_bsrli_epi128 v_IMM8) (IV.e_mm256_bsrli_epi128 v_IMM8) (IVL.e_mm256_bsrli_epi128' v_IMM8) rt_i128x2 a

let lemma_mm256_set1_epi64x (a: i64)
  : Lemma (to_i64x4 (Avx.e_mm256_set1_epi64x a) == IV.e_mm256_set1_epi64x a) =
  IVL.e_mm256_set1_epi64x' a;
  rt_i64x4 (IV.e_mm256_set1_epi64x a)

let lemma_mm256_set_epi64x (e3: i64) (e2: i64) (e1: i64) (e0: i64)
  : Lemma (to_i64x4 (Avx.e_mm256_set_epi64x e3 e2 e1 e0) == IV.e_mm256_set_epi64x e3 e2 e1 e0) =
  IVL.e_mm256_set_epi64x' e3 e2 e1 e0;
  rt_i64x4 (IV.e_mm256_set_epi64x e3 e2 e1 e0)

let lemma_mm256_unpacklo_epi64 (a: bv256) (b: bv256)
  : Lemma (to_i64x4 (Avx2.e_mm256_unpacklo_epi64 a b) == IV.e_mm256_unpacklo_epi64 (to_i64x4 a) (to_i64x4 b)) =
  op_lemma_from_lift_bin to_i64x4 from_i64x4 to_i64x4
    Avx2.e_mm256_unpacklo_epi64 IV.e_mm256_unpacklo_epi64 IVL.e_mm256_unpacklo_epi64' rt_i64x4 a b

let lemma_mm256_permute2x128_si256 (v_IMM8: i32) (a: bv256) (b: bv256)
  : Lemma (to_i128x2 (Avx2.e_mm256_permute2x128_si256 v_IMM8 a b) == IV.e_mm256_permute2x128_si256 v_IMM8 (to_i128x2 a) (to_i128x2 b)) =
  op_lemma_from_lift_bin to_i128x2 from_i128x2 to_i128x2
    (Avx2.e_mm256_permute2x128_si256 v_IMM8) (IV.e_mm256_permute2x128_si256 v_IMM8) (IVL.e_mm256_permute2x128_si256' v_IMM8) rt_i128x2 a b

let lemma_mm_sub_epi16 (a: bv128) (b: bv128)
  : Lemma (to_i16x8 (Sse2.e_mm_sub_epi16 a b) == IV.e_mm_sub_epi16 (to_i16x8 a) (to_i16x8 b)) =
  op_lemma_from_lift_bin to_i16x8 from_i16x8 to_i16x8
    Sse2.e_mm_sub_epi16 IV.e_mm_sub_epi16 IVL.e_mm_sub_epi16' rt_i16x8 a b

let lemma_mm256_cmpeq_epi32 (a: bv256) (b: bv256)
  : Lemma (to_i32x8 (Avx2.e_mm256_cmpeq_epi32 a b) == IV.e_mm256_cmpeq_epi32 (to_i32x8 a) (to_i32x8 b)) =
  op_lemma_from_lift_bin to_i32x8 from_i32x8 to_i32x8
    Avx2.e_mm256_cmpeq_epi32 IV.e_mm256_cmpeq_epi32 IVL.e_mm256_cmpeq_epi32' rt_i32x8 a b

let lemma_mm256_castsi256_si128 (a: bv256)
  : Lemma (Avx.e_mm256_castsi256_si128 a == IV.e_mm256_castsi256_si128 a) =
  IVL.e_mm256_castsi256_si128' a

let lemma_mm256_extracti128_si256 (v_IMM8: i32) (a: bv256)
  : Lemma (Avx2.e_mm256_extracti128_si256 v_IMM8 a == IV.e_mm256_extracti128_si256 v_IMM8 a) =
  IVL.e_mm256_extracti128_si256' v_IMM8 a

let lemma_mm256_slli_epi16 (v_IMM8: i32) (a: bv256)
  : Lemma (to_i16x16 (Avx2.e_mm256_slli_epi16 v_IMM8 a) == IV.e_mm256_slli_epi16 v_IMM8 (to_i16x16 a)) =
  op_lemma_from_lift_un to_i16x16 from_i16x16 to_i16x16
    (Avx2.e_mm256_slli_epi16 v_IMM8) (IV.e_mm256_slli_epi16 v_IMM8) (IVL.e_mm256_slli_epi16' v_IMM8) rt_i16x16 a

let lemma_mm256_srli_epi64 (v_IMM8: i32) (a: bv256)
  : Lemma (to_i64x4 (Avx2.e_mm256_srli_epi64 v_IMM8 a) == IV.e_mm256_srli_epi64 v_IMM8 (to_i64x4 a)) =
  op_lemma_from_lift_un to_i64x4 from_i64x4 to_i64x4
    (Avx2.e_mm256_srli_epi64 v_IMM8) (IV.e_mm256_srli_epi64 v_IMM8) (IVL.e_mm256_srli_epi64' v_IMM8) rt_i64x4 a

let lemma_mm256_sllv_epi32 (a: bv256) (b: bv256)
  : Lemma (to_i32x8 (Avx2.e_mm256_sllv_epi32 a b) == IV.e_mm256_sllv_epi32 (to_i32x8 a) (to_i32x8 b)) =
  op_lemma_from_lift_bin to_i32x8 from_i32x8 to_i32x8
    Avx2.e_mm256_sllv_epi32 IV.e_mm256_sllv_epi32 IVL.e_mm256_sllv_epi32' rt_i32x8 a b

let lemma_mm256_srlv_epi32 (a: bv256) (b: bv256)
  : Lemma (to_i32x8 (Avx2.e_mm256_srlv_epi32 a b) == IV.e_mm256_srlv_epi32 (to_i32x8 a) (to_i32x8 b)) =
  op_lemma_from_lift_bin to_i32x8 from_i32x8 to_i32x8
    Avx2.e_mm256_srlv_epi32 IV.e_mm256_srlv_epi32 IVL.e_mm256_srlv_epi32' rt_i32x8 a b

let lemma_mm256_permutevar8x32_epi32 (a: bv256) (b: bv256)
  : Lemma (to_i32x8 (Avx2.e_mm256_permutevar8x32_epi32 a b) == IV.e_mm256_permutevar8x32_epi32 (to_i32x8 a) (to_i32x8 b)) =
  op_lemma_from_lift_bin to_i32x8 from_i32x8 to_i32x8
    Avx2.e_mm256_permutevar8x32_epi32 IV.e_mm256_permutevar8x32_epi32 IVL.e_mm256_permutevar8x32_epi32' rt_i32x8 a b

let lemma_mm256_shuffle_epi8 (a: bv256) (b: bv256)
  : Lemma (to_i8x32 (Avx2.e_mm256_shuffle_epi8 a b) == IV.e_mm256_shuffle_epi8 (to_i8x32 a) (to_i8x32 b)) =
  op_lemma_from_lift_bin to_i8x32 from_i8x32 to_i8x32
    Avx2.e_mm256_shuffle_epi8 IV.e_mm256_shuffle_epi8 IVL.e_mm256_shuffle_epi8' rt_i8x32 a b

let lemma_mm_set_epi8 (e15: i8) (e14: i8) (e13: i8) (e12: i8) (e11: i8) (e10: i8) (e9: i8) (e8: i8) (e7: i8) (e6: i8) (e5: i8) (e4: i8) (e3: i8) (e2: i8) (e1: i8) (e0: i8)
  : Lemma (to_i8x16 (Sse2.e_mm_set_epi8 e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0) == IV.e_mm_set_epi8 e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0) =
  IVL.e_mm_set_epi8' e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0;
  rt_i8x16 (IV.e_mm_set_epi8 e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0)

let lemma_mm256_set_epi8 (e31: i8) (e30: i8) (e29: i8) (e28: i8) (e27: i8) (e26: i8) (e25: i8) (e24: i8) (e23: i8) (e22: i8) (e21: i8) (e20: i8) (e19: i8) (e18: i8) (e17: i8) (e16: i8) (e15: i8) (e14: i8) (e13: i8) (e12: i8) (e11: i8) (e10: i8) (e9: i8) (e8: i8) (e7: i8) (e6: i8) (e5: i8) (e4: i8) (e3: i8) (e2: i8) (e1: i8) (e0: i8)
  : Lemma (to_i8x32 (Avx.e_mm256_set_epi8 e31 e30 e29 e28 e27 e26 e25 e24 e23 e22 e21 e20 e19 e18 e17 e16 e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0) == IV.e_mm256_set_epi8 e31 e30 e29 e28 e27 e26 e25 e24 e23 e22 e21 e20 e19 e18 e17 e16 e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0) =
  IVL.e_mm256_set_epi8' e31 e30 e29 e28 e27 e26 e25 e24 e23 e22 e21 e20 e19 e18 e17 e16 e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0;
  rt_i8x32 (IV.e_mm256_set_epi8 e31 e30 e29 e28 e27 e26 e25 e24 e23 e22 e21 e20 e19 e18 e17 e16 e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0)

let lemma_mm256_set_epi16 (e15: i16) (e14: i16) (e13: i16) (e12: i16) (e11: i16) (e10: i16) (e9: i16) (e8: i16) (e7: i16) (e6: i16) (e5: i16) (e4: i16) (e3: i16) (e2: i16) (e1: i16) (e0: i16)
  : Lemma (to_i16x16 (Avx.e_mm256_set_epi16 e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0) == IV.e_mm256_set_epi16 e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0) =
  IVL.e_mm256_set_epi16' e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0;
  rt_i16x16 (IV.e_mm256_set_epi16 e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0)

let lemma_mm256_set_epi32 (e7: i32) (e6: i32) (e5: i32) (e4: i32) (e3: i32) (e2: i32) (e1: i32) (e0: i32)
  : Lemma (to_i32x8 (Avx.e_mm256_set_epi32 e7 e6 e5 e4 e3 e2 e1 e0) == IV.e_mm256_set_epi32 e7 e6 e5 e4 e3 e2 e1 e0) =
  IVL.e_mm256_set_epi32' e7 e6 e5 e4 e3 e2 e1 e0;
  rt_i32x8 (IV.e_mm256_set_epi32 e7 e6 e5 e4 e3 e2 e1 e0)

let lemma_mm_setzero_si128 (u: Prims.unit)
  : Lemma (Sse2.e_mm_setzero_si128 () == IV.e_mm_setzero_si128 ()) =
  IVL.e_mm_setzero_si128' ()

let lemma_mm_xor_si128 (a: bv128) (b: bv128)
  : Lemma (Sse2.e_mm_xor_si128 a b == IV.e_mm_xor_si128 a b) =
  IVL.e_mm_xor_si128' a b

let lemma_mm_shuffle_epi32 (v_IMM8: i32) (a: bv128)
  : Lemma (to_i32x4 (Sse2.e_mm_shuffle_epi32 v_IMM8 a) == IV.e_mm_shuffle_epi32 v_IMM8 (to_i32x4 a)) =
  op_lemma_from_lift_un to_i32x4 from_i32x4 to_i32x4
    (Sse2.e_mm_shuffle_epi32 v_IMM8) (IV.e_mm_shuffle_epi32 v_IMM8) (IVL.e_mm_shuffle_epi32' v_IMM8) rt_i32x4 a

let lemma_mm_unpackhi_epi64 (a: bv128) (b: bv128)
  : Lemma (to_i64x2 (Sse2.e_mm_unpackhi_epi64 a b) == IV.e_mm_unpackhi_epi64 (to_i64x2 a) (to_i64x2 b)) =
  op_lemma_from_lift_bin to_i64x2 from_i64x2 to_i64x2
    Sse2.e_mm_unpackhi_epi64 IV.e_mm_unpackhi_epi64 IVL.e_mm_unpackhi_epi64' rt_i64x2 a b

let lemma_mm_unpacklo_epi64 (a: bv128) (b: bv128)
  : Lemma (to_i64x2 (Sse2.e_mm_unpacklo_epi64 a b) == IV.e_mm_unpacklo_epi64 (to_i64x2 a) (to_i64x2 b)) =
  op_lemma_from_lift_bin to_i64x2 from_i64x2 to_i64x2
    Sse2.e_mm_unpacklo_epi64 IV.e_mm_unpacklo_epi64 IVL.e_mm_unpacklo_epi64' rt_i64x2 a b

let lemma_mm_slli_si128 (v_IMM8: i32) (a: bv128)
  : Lemma (to_i8x16 (Sse2.e_mm_slli_si128 v_IMM8 a) == IV.e_mm_slli_si128 v_IMM8 (to_i8x16 a)) =
  op_lemma_from_lift_un to_i8x16 from_i8x16 to_i8x16
    (Sse2.e_mm_slli_si128 v_IMM8) (IV.e_mm_slli_si128 v_IMM8) (IVL.e_mm_slli_si128' v_IMM8) rt_i8x16 a

let lemma_mm_srli_si128 (v_IMM8: i32) (a: bv128)
  : Lemma (to_i8x16 (Sse2.e_mm_srli_si128 v_IMM8 a) == IV.e_mm_srli_si128 v_IMM8 (to_i8x16 a)) =
  op_lemma_from_lift_un to_i8x16 from_i8x16 to_i8x16
    (Sse2.e_mm_srli_si128 v_IMM8) (IV.e_mm_srli_si128 v_IMM8) (IVL.e_mm_srli_si128' v_IMM8) rt_i8x16 a

let lemma_mm256_mullo_epi16 (a: bv256) (b: bv256)
  : Lemma (to_i16x16 (Avx2.e_mm256_mullo_epi16 a b) == IV.e_mm256_mullo_epi16 (to_i16x16 a) (to_i16x16 b)) =
  op_lemma_from_lift_bin to_i16x16 from_i16x16 to_i16x16
    Avx2.e_mm256_mullo_epi16 IV.e_mm256_mullo_epi16 IVL.e_mm256_mullo_epi16' rt_i16x16 a b

let lemma_mm256_madd_epi16 (a: bv256) (b: bv256)
  : Lemma (to_i32x8 (Avx2.e_mm256_madd_epi16 a b) == IV.e_mm256_madd_epi16 (to_i16x16 a) (to_i16x16 b)) =
  op_lemma_from_lift_bin to_i16x16 from_i32x8 to_i32x8
    Avx2.e_mm256_madd_epi16 IV.e_mm256_madd_epi16 IVL.e_mm256_madd_epi16' rt_i32x8 a b

let lemma_mm_shuffle_epi8 (a: bv128) (b: bv128)
  : Lemma (to_i8x16 (Ssse3.e_mm_shuffle_epi8 a b) == IV.e_mm_shuffle_epi8 (to_i8x16 a) (to_i8x16 b)) =
  op_lemma_from_lift_bin to_i8x16 from_i8x16 to_i8x16
    Ssse3.e_mm_shuffle_epi8 IV.e_mm_shuffle_epi8 IVL.e_mm_shuffle_epi8' rt_i8x16 a b

(* ============================================================================
   Task B: movemask bit companion — bit i of the movemask == sign bit of lane i.
   Discharged over the core-models movemask FOLD model (`e_movemask_bit_sum_*`,
   Int_vec.fst, a base-2 LSB-first accumulation of lane sign bits) by digit
   extraction.  This is the bit-level shape the serialize spike (serialize_1 /
   rejection_sample) needs; it was previously an ASSUMED companion.
   ============================================================================ *)
module MLem = FStar.Math.Lemmas

(* per-lane sign-bit readers over the canonical i8/i32 lane views *)
let sign_bit8 (a: Funarr.t_FunArray (mk_u64 16) i8) (i: nat{i < 16}) : n: nat{n < 2} =
  if (a.[ mk_u64 i ] <: i8) <. mk_i8 0 then 1 else 0
let sign_bit32 (a: Funarr.t_FunArray (mk_u64 8) i32) (i: nat{i < 8}) : n: nat{n < 2} =
  if (a.[ mk_u64 i ] <: i32) <. mk_i32 0 then 1 else 0

(* digit extraction: bit (i-off) of the base-2 fold == lane i's sign bit *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let rec digit_i8 (a: Funarr.t_FunArray (mk_u64 16) i8) (off n: nat)
    (i: nat{off <= i /\ i < off + n /\ off + n <= 16})
    : Lemma (ensures (IV.e_movemask_bit_sum_i8 a off n / pow2 (i - off)) % 2 == sign_bit8 a i)
            (decreases n) =
  let b0 = (if (a.[ mk_u64 off ] <: i8) <. mk_i8 0 then 1 else 0) in
  let rest = IV.e_movemask_bit_sum_i8 a (off + 1) (n - 1) in
  if i = off then (assert_norm (pow2 0 == 1); MLem.lemma_mod_plus b0 rest 2; MLem.small_mod b0 2)
  else (let k = i - off in
        digit_i8 a (off + 1) (n - 1) i;
        MLem.lemma_div_plus b0 rest 2; MLem.small_div b0 2;
        MLem.pow2_plus 1 (k - 1);
        MLem.division_multiplication_lemma (IV.e_movemask_bit_sum_i8 a off n) 2 (pow2 (k - 1)))

let rec digit_i32 (a: Funarr.t_FunArray (mk_u64 8) i32) (off n: nat)
    (i: nat{off <= i /\ i < off + n /\ off + n <= 8})
    : Lemma (ensures (IV.e_movemask_bit_sum_i32 a off n / pow2 (i - off)) % 2 == sign_bit32 a i)
            (decreases n) =
  let b0 = (if (a.[ mk_u64 off ] <: i32) <. mk_i32 0 then 1 else 0) in
  let rest = IV.e_movemask_bit_sum_i32 a (off + 1) (n - 1) in
  if i = off then (assert_norm (pow2 0 == 1); MLem.lemma_mod_plus b0 rest 2; MLem.small_mod b0 2)
  else (let k = i - off in
        digit_i32 a (off + 1) (n - 1) i;
        MLem.lemma_div_plus b0 rest 2; MLem.small_div b0 2;
        MLem.pow2_plus 1 (k - 1);
        MLem.division_multiplication_lemma (IV.e_movemask_bit_sum_i32 a off n) 2 (pow2 (k - 1)))
#pop-options

(* bit i of the movemask MODEL value == sign bit of lane i of the FunArray view *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let movemask_epi8_model_bit (a: Funarr.t_FunArray (mk_u64 16) i8) (i: nat{i < 16})
    : Lemma ((v (IV.e_mm_movemask_epi8 a) / pow2 i) % 2 == sign_bit8 a i) =
  IV.e_movemask_bit_sum_i8_bound a 0 16; assert_norm (pow2 16 == 65536);
  digit_i8 a 0 16 i

let movemask_ps_model_bit (a: Funarr.t_FunArray (mk_u64 8) i32) (i: nat{i < 8})
    : Lemma ((v (IV.e_mm256_movemask_ps a) / pow2 i) % 2 == sign_bit32 a i) =
  IV.e_movemask_bit_sum_i32_bound a 0 8; assert_norm (pow2 8 == 256);
  digit_i32 a 0 8 i
#pop-options

(* DELIVERABLE bit companions over the TESTED Sse2/Avx movemask ops: bit i of the
   movemask == sign bit of lane i of the canonical `to_i8x16` / `to_i32x8` view. *)
let movemask_epi8_bit (a: bv128) (i: nat{i < 16})
    : Lemma ((v (Sse2.e_mm_movemask_epi8 a) / pow2 i) % 2 == sign_bit8 (to_i8x16 a) i) =
  lemma_mm_movemask_epi8 a;
  movemask_epi8_model_bit (to_i8x16 a) i

let movemask_ps_bit (a: bv256) (i: nat{i < 8})
    : Lemma ((v (Avx.e_mm256_movemask_ps a) / pow2 i) % 2 == sign_bit32 (to_i32x8 a) i) =
  lemma_mm256_movemask_ps a;
  movemask_ps_model_bit (to_i32x8 a) i
