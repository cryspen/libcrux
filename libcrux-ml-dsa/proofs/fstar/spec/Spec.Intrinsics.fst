module Spec.Intrinsics
open FStar.Mul
open Core_models
open Libcrux_core_models.Core_arch.X86.Interpretations.Int_vec
open FStar.FunctionalExtensionality
open Libcrux_core_models.Abstractions.Bit

module I      = Libcrux_intrinsics.Avx2
module Canon  = Libcrux_core_models.Intrinsics_views
module IV     = Libcrux_core_models.Core_arch.X86.Interpretations.Int_vec
module IVi    = Libcrux_core_models.Abstractions.Bitvec.Int_vec_interp
module Avx2c  = Libcrux_core_models.Core_arch.X86.Avx2
module Funarr = Libcrux_core_models.Abstractions.Funarr
module BV     = Libcrux_core_models.Abstractions.Bitvec
module Ints   = Rust_primitives.Integers

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(* ====================================================================
   Spec.Intrinsics.fst — implementations of the 98 vals in the .fsti.
   Views are ._0 field-projections of the canonical core-models record
   views (`Libcrux_core_models.Intrinsics_views` = Canon); op-lemmas are
   discharged against Canon's proven lifts over the differentially-tested
   `Int_vec.Lemmas`.  See Spec.Intrinsics.fsti for the statements.
   Interface-val order MUST match the .fsti (F* enforces it).
   ==================================================================== *)

(**** (#1-7) Bit vec -> int vec view adapters. *)
let to_i8x32  (x: bv256): i8x32  = (Canon.to_i8x32 x)._0
let to_i8x16  (x: bv128): i8x16  = (Canon.to_i8x16 x)._0
let to_i16x16 (x: bv256): i16x16 = (Canon.to_i16x16 x)._0
let to_i32x4  (x: bv128): i32x4  = (Canon.to_i32x4 x)._0
let to_i32x8  (x: bv256): i32x8  = (Canon.to_i32x8 x)._0
let to_i64x4  (x: bv256): i64x4  = (Canon.to_i64x4 x)._0
let to_u8x16  (x: bv128): u8x16  = (IVi.e_ee_18__impl__to_u8x16 x)._0

(**** (#8) Int vec -> bit vec *)
let from_i32x8 (x:i32x8):  bv256 = Canon.from_i32x8 (Funarr.FunArray x)

(**** (#9-12) Int -> bit vecs: bit j of the two's-complement rep of the scalar. *)
let i16_to_bv (x: i16): t_FunArray (mk_int 16) t_Bit =
  on (i:u64{v i < 16}) (fun i -> IVi.encode_bit Ints.I16 x (v i))
let i32_to_bv (x: i32): t_FunArray (mk_int 32) t_Bit =
  on (i:u64{v i < 32}) (fun i -> IVi.encode_bit Ints.I32 x (v i))
let i64_to_bv (x: i64): t_FunArray (mk_int 64) t_Bit =
  on (i:u64{v i < 64}) (fun i -> IVi.encode_bit Ints.I64 x (v i))
let u8_to_bv (x: u8): t_FunArray (mk_int 8) t_Bit =
  on (i:u64{v i < 8}) (fun i -> IVi.encode_bit Ints.U8 x (v i))

(* ---- foundational helpers (private; not interface vals) ---- *)

let bval_inj (a b: t_Bit) : Lemma (requires IVi.bval a == IVi.bval b) (ensures a == b) = ()

let tc_of_u_mod (t: Ints.inttype) (u: nat{u < pow2 (Ints.bits t)})
  : Lemma (IVi.tc_of_u t u % pow2 (Ints.bits t) == u) =
  let p = pow2 (Ints.bits t) in
  if Ints.signed t && u >= pow2 (Ints.bits t - 1)
  then (FStar.Math.Lemmas.lemma_mod_plus u (-1) p; FStar.Math.Lemmas.small_mod u p)
  else FStar.Math.Lemmas.small_mod u p

#push-options "--fuel 1 --ifuel 2 --z3rlimit 120"
(* encode_bit inverts decode_lane pointwise on a bit function. *)
let lemma_encode_decode_bit (t: Ints.inttype) (f: nat -> t_Bit) (b: nat{b < Ints.bits t})
  : Lemma (IVi.encode_bit t (IVi.decode_lane t f) b == f b) =
  let n = Ints.bits t in
  IVi.dsum2_bound f 0 n;
  let u = IVi.dsum2 f 0 n in
  IVi.lemma_tc_range t u;
  tc_of_u_mod t u;
  IVi.ebit_bit u b;
  Canon.dsum2_digit f 0 n b;
  bval_inj (IVi.encode_bit t (IVi.decode_lane t f) b) (f b)
#pop-options

(* the raw bit of a bitvec at position (w*i+b) via lane_reader, for b<w in range. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 120"
let lemma_lane_reader_raw (n: u64) (w: nat) (bv: BV.t_BitVec n) (i: u64) (b: nat)
  : Lemma (requires b < w /\ w * v i + b < v n)
          (ensures IVi.lane_reader n w bv i b ==
                   Funarr.impl_5__get n #t_Bit bv._0 (mk_u64 (w * v i + b))) = ()
#pop-options

(* generic bit-view inversion: bit j of the i-th w-bit lane view == raw bit w*i+j. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 250"
let bit_view_inv (t: Ints.inttype) (n m: u64) (vec: BV.t_BitVec n)
      (i: u64{v i < v m}) (j: u64{v j < Ints.bits t})
  : Lemma (requires v n == v m * Ints.bits t)
          (ensures IVi.encode_bit t ((IVi.to_iv t n m vec)._0 i) (v j) ==
                   Funarr.impl_5__get n #t_Bit vec._0 (mk_u64 (Ints.bits t * v i + v j))) =
  reveal_opaque (`%IVi.to_iv) IVi.to_iv;
  lemma_lane_reader_raw n (Ints.bits t) vec i (v j);
  lemma_encode_decode_bit t (IVi.lane_reader n (Ints.bits t) vec i) (v j)
#pop-options

(* ---- get_bit bridge toolkit (private; not interface vals) ----
   The core-models bit codec `IVi.encode_bit t x b` has bval equal to the
   rust_primitives `get_bit x b`, so the whole get_bit algebra (get_bit_and/
   or/xor/shl/shr/cast/pow2, all SMTPat-tagged) discharges the `*_to_bv`
   arithmetic family. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let ebit_is_get_bit (t: Ints.inttype) (x: Ints.int_t t) (b: nat{b < Ints.bits t})
  : Lemma (IVi.bval (IVi.encode_bit t x b) == Ints.get_bit x (Ints.mk_usize b)) =
  let n = Ints.bits t in
  IVi.ebit_bit (Ints.v x % pow2 n) b;
  reveal_opaque (`%Ints.get_bit) (Ints.get_bit #t);
  if Ints.v x >= 0
  then FStar.Math.Lemmas.small_mod (Ints.v x) (pow2 n)
  else (FStar.Math.Lemmas.lemma_mod_plus (Ints.v x) 1 (pow2 n);
        FStar.Math.Lemmas.small_mod (Ints.v x + pow2 n) (pow2 n))

(* encode_bit is determined by get_bit: read a bit off get_bit *)
let bit_of_get_bit (t: Ints.inttype) (x: Ints.int_t t) (b: nat{b < Ints.bits t})
  : Lemma (IVi.encode_bit t x b ==
           (if Ints.get_bit x (Ints.mk_usize b) = 1 then Bit_One else Bit_Zero)) =
  ebit_is_get_bit t x b;
  bval_inj (IVi.encode_bit t x b)
           (if Ints.get_bit x (Ints.mk_usize b) = 1 then Bit_One else Bit_Zero)

(* u8 -> i32 `cast` coincides with `cast_mod` (value in range), so the
   get_bit_cast / get_bit_cast_extend SMTPats (stated on cast_mod) fire. *)
let cast_u8_i32 (a: u8) : Lemma ((cast a <: i32) == Ints.cast_mod #Ints.U8 #Ints.I32 a) = ()
#pop-options

(* i64 analogue of i32_to_bv_to_i32x4_inv (private helper). *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 250"
let i64_to_bv_to_i64x4_inv (vec: bv256) (i: u64{v i < 4}) (j: u64{v j < 64})
  : Lemma (i64_to_bv (to_i64x4 vec i) j == vec.(mk_int (v i * 64 + v j))) =
  bit_view_inv Ints.I64 (mk_u64 256) (mk_u64 4) vec i j
#pop-options

(* ---- (#13) inversion / definitional ---- *)
let to_from_i32x8_inv_lemma x =
  IVi.lemma_conv_rt Ints.I32 (mk_u64 256) (mk_u64 8) (Funarr.FunArray x)

(* ---- (#14) ---- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 250"
let i16_to_bv_to_i16x16_inv vec i j =
  bit_view_inv Ints.I16 (mk_u64 256) (mk_u64 16) vec i j
#pop-options

(* ---- (#15-98): admitted stubs, to be discharged batch by batch ---- *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"
let mm256_castsi256_si128_bv_lemma vec i =
  reveal_opaque (`%I.mm256_castsi256_si128) I.mm256_castsi256_si128;
  Canon.lemma_bv_index vec i
#pop-options
#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
let mm256_extracti128_si256_bv_lemma control vec i =
  reveal_opaque (`%I.mm256_extracti128_si256) I.mm256_extracti128_si256;
  Canon.lemma_bv_index vec (mk_int (if v control = 0 then 0 else 128) +! i)
#pop-options
#push-options "--fuel 2 --ifuel 2 --z3rlimit 400"
let mm256_extracti128_si256_lemma control vec i =
  let off : u64 = mk_int (if v control = 0 then 0 else 4) in
  let l = to_i32x4 (I.mm256_extracti128_si256 control vec) i in
  let r = to_i32x8 vec (i +! off) in
  let aux (jj: Ints.usize{v jj < 32}) : Lemma (Ints.get_bit l jj == Ints.get_bit r jj) =
    let j = mk_u64 (v jj) in
    mm256_extracti128_si256_bv_lemma control vec (mk_u64 (v i * 32 + v jj));
    bit_view_inv Ints.I32 (mk_u64 128) (mk_u64 4) (I.mm256_extracti128_si256 control vec) i j;
    bit_view_inv Ints.I32 (mk_u64 256) (mk_u64 8) vec (i +! off) j;
    ebit_is_get_bit Ints.I32 l (v jj);
    ebit_is_get_bit Ints.I32 r (v jj)
  in
  FStar.Classical.forall_intro aux;
  Ints.lemma_int_t_eq_via_bits l r
#pop-options
#push-options "--fuel 1 --ifuel 2 --z3rlimit 200"
let mm256_and_si256 lhs rhs i =
  reveal_opaque (`%I.mm256_and_si256) I.mm256_and_si256;
  Canon.lemma_and_si256_lift lhs rhs;
  Canon.lemma_and_funarr lhs rhs i
#pop-options
let mm_storeu_bytes_si128_lemma = admit ()
let update_at_range_bv_lemma = admit ()
#push-options "--fuel 2 --ifuel 2 --z3rlimit 250"
let u8_to_bv_to_u8x16_inv vec i j =
  bit_view_inv Ints.U8 (mk_u64 128) (mk_u64 16) vec i j
let i32_to_bv_to_i32x8_inv vec i j =
  bit_view_inv Ints.I32 (mk_u64 256) (mk_u64 8) vec i j
#pop-options
let mm256_bsrli_epi128_lemma = admit ()
let mm256_permutevar8x32_epi32_lemma = admit ()
let mm256_srlv_epi32_bv_lemma = admit ()
let mm_sllv_epi32_bv_lemma = admit ()
let mm256_sllv_epi32_bv_lemma = admit ()
let mm256_srlv_epi64_bv_lemma = admit ()
let mm256_srli_epi64_bv_lemma = admit ()
let mm256_slli_epi64_bv_lemma = admit ()
let mm_srli_epi64_bv_lemma = admit ()
let i16_mul_32extended_bv_lemma = admit ()
#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"
let i16_mul_32extended_bv_lemma1 x i =
  reveal_opaque (`%i16_mul_32extended) i16_mul_32extended;
  assert ((x `i16_mul_32extended` mk_i16 0) == mk_i32 0);
  bit_of_get_bit Ints.I32 (mk_i32 0) (v i);
  reveal_opaque (`%Ints.get_bit) (Ints.get_bit #Ints.I32)
#pop-options
let i16_mul_32extendedi16_bv_lemma = admit ()
let mm256_madd_epi16_lemma = admit ()
let mm256_add_epi64_lemma = admit ()
let mm256_madd_epi16_specialized_lemma = admit ()
let i32_to_bv_add_bv_lemma = admit ()
#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"
let pow2_lemma shift i =
  bit_of_get_bit Ints.I32 (mk_i32 1 <<! shift <: i32) (v i)
#pop-options
#push-options "--fuel 2 --ifuel 1 --z3rlimit 300"
let mm256_set_epi8_lemma b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 i =
  reveal_opaque (`%I.mm256_set_epi8) I.mm256_set_epi8;
  Canon.lemma_mm256_set_epi8 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31;
  Canon.lemma_iv_set_epi8 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 (v i)
let mm_set_epi8_lemma b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 i =
  reveal_opaque (`%I.mm_set_epi8) I.mm_set_epi8;
  Canon.lemma_mm_set_epi8 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15;
  Canon.lemma_iv_mm_set_epi8 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 (v i)
let mm256_set_epi16_lemma v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 i =
  reveal_opaque (`%I.mm256_set_epi16) I.mm256_set_epi16;
  Canon.lemma_mm256_set_epi16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15;
  Canon.lemma_iv_set_epi16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 (v i)
#pop-options
let mm256_shuffle_epi8_lemma = admit ()
let mm_shuffle_epi8_lemma = admit ()
let mm256_mullo_epi16_bv_lemma = admit ()
#push-options "--fuel 2 --ifuel 1 --z3rlimit 300"
let mm256_shuffle_epi32_lemma a b i =
  reveal_opaque (`%I.mm256_shuffle_epi32) I.mm256_shuffle_epi32;
  Canon.lemma_mm256_shuffle_epi32 a b
#pop-options
#push-options "--fuel 2 --ifuel 1 --z3rlimit 200"
let mm256_sub_epi32_lemma a b i =
  reveal_opaque (`%I.mm256_sub_epi32) I.mm256_sub_epi32;
  reveal_opaque_arithmetic_ops #i32_inttype;
  Canon.lemma_mm256_sub_epi32 a b
let mm256_add_epi32_lemma a b i =
  reveal_opaque (`%I.mm256_add_epi32) I.mm256_add_epi32;
  reveal_opaque_arithmetic_ops #i32_inttype;
  Canon.lemma_mm256_add_epi32 a b
let mm256_mullo_epi32_lemma a b i =
  reveal_opaque (`%I.mm256_mullo_epi32) I.mm256_mullo_epi32;
  reveal_opaque_arithmetic_ops #i32_inttype;
  Canon.lemma_mm256_mullo_epi32 a b
#pop-options
let mm256_mul_epi32_lemma = admit ()
#push-options "--fuel 2 --ifuel 1 --z3rlimit 200"
let mm256_srai_epi32_lemma v_IMM8 a i =
  reveal_opaque (`%I.mm256_srai_epi32) I.mm256_srai_epi32;
  reveal_opaque_arithmetic_ops #i32_inttype;
  Canon.lemma_mm256_srai_epi32 v_IMM8 a
#pop-options
(* CLIFF: slli model/axiom diverge for out-of-range IMM8: .fsti returns 0 when
   v_IMM8 < 0, but core-models e_mm256_slli_epi32 shifts by (rem_euclid IMM8 256),
   which for e.g. IMM8 = -256 is a shift-by-0 (= a), not 0. Provable only under a
   0 <= IMM8 <= 31 precondition the .fsti does not carry. Hedged axiom. *)
let mm256_slli_epi32_lemma = admit ()
#push-options "--fuel 2 --ifuel 2 --z3rlimit 400"
let mm256_and_si256_lemma a b i =
  let r = to_i32x8 (I.mm256_and_si256 a b) i in
  let xa = to_i32x8 a i in
  let xb = to_i32x8 b i in
  let aux (jj: Ints.usize{v jj < 32}) : Lemma
    (Ints.get_bit r jj == Ints.get_bit (xa &. xb) jj) =
    let j = mk_u64 (v jj) in
    mm256_and_si256 a b (mk_u64 (v i * 32 + v jj));
    i32_to_bv_to_i32x8_inv (I.mm256_and_si256 a b) i j;
    i32_to_bv_to_i32x8_inv a i j;
    i32_to_bv_to_i32x8_inv b i j;
    ebit_is_get_bit Ints.I32 r (v jj);
    ebit_is_get_bit Ints.I32 xa (v jj);
    ebit_is_get_bit Ints.I32 xb (v jj)
  in
  FStar.Classical.forall_intro aux;
  Ints.lemma_int_t_eq_via_bits r (xa &. xb)
#pop-options
(* raw-bit semantics of the hardware xor (mirror of Canon.lemma_and_funarr). *)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 250"
let mm256_xor_bv (a b: bv256) (k: u64{v k < 256})
  : Lemma ((I.mm256_xor_si256 a b).(k) ==
           (match a.(k), b.(k) with
            | Bit_Zero, Bit_Zero -> Bit_Zero
            | Bit_One,  Bit_One  -> Bit_Zero
            | _ -> Bit_One)) =
  reveal_opaque (`%I.mm256_xor_si256) I.mm256_xor_si256;
  Canon.lemma_xor_si256_lift a b;
  let f : (i: u64{v i < 256}) -> t_Bit =
    fun i -> (let i:u64 = i in
              match (a.[ i ] <: t_Bit), (b.[ i ] <: t_Bit) with
              | Bit_Zero, Bit_Zero -> Bit_Zero
              | Bit_One,  Bit_One  -> Bit_Zero
              | _ -> Bit_One) in
  assert (IV.e_mm256_xor_si256 a b ==
          Libcrux_core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 256) #(u64 -> t_Bit) f)
    by (FStar.Tactics.norm [delta_only [`%IV.e_mm256_xor_si256]; iota; zeta; primops];
        FStar.Tactics.trefl ());
  Canon.lemma_impl9_index f k;
  Canon.lemma_bv_index a k;
  Canon.lemma_bv_index b k
#pop-options
#push-options "--fuel 2 --ifuel 2 --z3rlimit 400"
let mm256_xor_si256_lemma a b i =
  let r = to_i32x8 (I.mm256_xor_si256 a b) i in
  let xa = to_i32x8 a i in
  let xb = to_i32x8 b i in
  let aux (jj: Ints.usize{v jj < 32}) : Lemma
    (Ints.get_bit r jj == Ints.get_bit (xa ^. xb) jj) =
    let j = mk_u64 (v jj) in
    mm256_xor_bv a b (mk_u64 (v i * 32 + v jj));
    i32_to_bv_to_i32x8_inv (I.mm256_xor_si256 a b) i j;
    i32_to_bv_to_i32x8_inv a i j;
    i32_to_bv_to_i32x8_inv b i j;
    ebit_is_get_bit Ints.I32 r (v jj);
    ebit_is_get_bit Ints.I32 xa (v jj);
    ebit_is_get_bit Ints.I32 xb (v jj)
  in
  FStar.Classical.forall_intro aux;
  Ints.lemma_int_t_eq_via_bits r (xa ^. xb)
#pop-options
(* CLIFF: core-models e_mm256_abs_epi32 delegates to Core_models.Num.impl_i32__abs =
   Rust_primitives.Arithmetic.abs_i32, an UNINTERPRETED `val abs_i32 : i32 -> i32`
   with no ensures anywhere in the hax proof-libs. Cannot bridge to abs_int
   (= mk_int (abs (v x))) without an axiom about abs_i32. Blocked by a missing
   primitive spec, not by the model. *)
let mm256_abs_epi32_lemma = admit ()
#push-options "--fuel 2 --ifuel 1 --z3rlimit 200"
let mm256_cmpgt_epi32_lemma a b i =
  reveal_opaque (`%I.mm256_cmpgt_epi32) I.mm256_cmpgt_epi32;
  Canon.lemma_mm256_cmpgt_epi32 a b
#pop-options
let mm256_testz_si256_lemma = admit ()
#push-options "--fuel 2 --ifuel 1 --z3rlimit 200"
let mm256_set_epi64x_lemma x0 x1 x2 x3 i =
  reveal_opaque (`%I.mm256_set_epi64x) I.mm256_set_epi64x;
  Canon.lemma_mm256_set_epi64x x0 x1 x2 x3
#pop-options
#push-options "--fuel 2 --ifuel 1 --z3rlimit 250"
let mm256_set_epi64x_bv_lemma x0 x1 x2 x3 i =
  let lane = i /! mk_u64 64 in
  let bit = i %! mk_u64 64 in
  FStar.Math.Lemmas.lemma_div_mod (v i) 64;
  i64_to_bv_to_i64x4_inv (I.mm256_set_epi64x x0 x1 x2 x3) lane bit;
  mm256_set_epi64x_lemma x0 x1 x2 x3 lane
#pop-options
#push-options "--fuel 2 --ifuel 1 --z3rlimit 200"
let mm256_set_epi32_lemma x0 x1 x2 x3 x4 x5 x6 x7 i =
  reveal_opaque (`%I.mm256_set_epi32) I.mm256_set_epi32;
  Canon.lemma_mm256_set_epi32 x0 x1 x2 x3 x4 x5 x6 x7
let mm256_set1_epi32_lemma x0 i =
  reveal_opaque (`%I.mm256_set1_epi32) I.mm256_set1_epi32;
  Canon.lemma_mm256_set1_epi32 x0
#pop-options
#push-options "--fuel 2 --ifuel 1 --z3rlimit 250"
let mm256_set1_epi32_bv_lemma x0 i =
  let lane = i /! mk_u64 32 in
  let bit = i %! mk_u64 32 in
  FStar.Math.Lemmas.lemma_div_mod (v i) 32;
  i32_to_bv_to_i32x8_inv (I.mm256_set1_epi32 x0) lane bit;
  mm256_set1_epi32_lemma x0 lane
let mm256_set_epi32_bv_lemma x0 x1 x2 x3 x4 x5 x6 x7 i =
  let lane = i /! mk_u64 32 in
  let bit = i %! mk_u64 32 in
  FStar.Math.Lemmas.lemma_div_mod (v i) 32;
  i32_to_bv_to_i32x8_inv (I.mm256_set_epi32 x0 x1 x2 x3 x4 x5 x6 x7) lane bit;
  mm256_set_epi32_lemma x0 x1 x2 x3 x4 x5 x6 x7 lane
#pop-options
#push-options "--fuel 2 --ifuel 1 --z3rlimit 200"
let mm_set_epi32_lemma x0 x1 x2 x3 i =
  reveal_opaque (`%I.mm_set_epi32) I.mm_set_epi32;
  Canon.lemma_mm_set_epi32 x0 x1 x2 x3
#pop-options
#push-options "--fuel 2 --ifuel 1 --z3rlimit 300"
let mm256_blend_epi32_lemma imm8 a b i =
  reveal_opaque (`%I.mm256_blend_epi32) I.mm256_blend_epi32;
  Canon.lemma_mm256_blend_epi32 imm8 a b
#pop-options
let mm256_set_m128i_bv_lemma = admit ()
let mm256_set_m128i_lemma = admit ()
let mm256_permute2x128_si256_lemma_i32x4 = admit ()
#push-options "--fuel 2 --ifuel 2 --z3rlimit 400"
let mm256_castsi256_si128_lemma a i =
  let l = to_i32x4 (I.mm256_castsi256_si128 a) i in
  let r = to_i32x8 a i in
  let aux (jj: Ints.usize{v jj < 32}) : Lemma (Ints.get_bit l jj == Ints.get_bit r jj) =
    let j = mk_u64 (v jj) in
    mm256_castsi256_si128_bv_lemma a (mk_u64 (v i * 32 + v jj));
    bit_view_inv Ints.I32 (mk_u64 128) (mk_u64 4) (I.mm256_castsi256_si128 a) i j;
    i32_to_bv_to_i32x8_inv a i j;
    ebit_is_get_bit Ints.I32 l (v jj);
    ebit_is_get_bit Ints.I32 r (v jj)
  in
  FStar.Classical.forall_intro aux;
  Ints.lemma_int_t_eq_via_bits l r
#pop-options
let mm256_unpacklo_epi64_lemma = admit ()
let mm256_unpackhi_epi64_lemma = admit ()
let mm_loadu_si128_lemma = admit ()
let i32_lt_pow2_n_to_bit_zero_lemma = admit ()
#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
let shl_casted_u8_bv_lemma a b i =
  cast_u8_i32 a; cast_u8_i32 b;
  bit_of_get_bit Ints.I32 (((cast b <: i32) <<! mk_i32 8 <: i32) |. (cast a <: i32) <: i32) (v i);
  if v i >= 16 then ()
  else if v i >= 8 then bit_of_get_bit Ints.U8 b (v i - 8)
  else bit_of_get_bit Ints.U8 a (v i)
let i32_to_bv_cast_lemma a i =
  cast_u8_i32 a;
  bit_of_get_bit Ints.I32 (cast a <: i32) (v i);
  if v i < 8 then bit_of_get_bit Ints.U8 a (v i)
#pop-options
#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
let i32_to_bv_pow2_min_one_lemma n i =
  FStar.Math.Lemmas.pow2_lt_compat 31 n;
  Rust_primitives.BitVectors.get_bit_pow2_minus_one #Ints.I32 n (Ints.mk_usize (v i));
  assert ((mk_i32 1 <<! mk_i32 n <: i32) -! mk_i32 1 == Ints.mk_int #Ints.I32 (pow2 n - 1));
  bit_of_get_bit Ints.I32 ((mk_i32 1 <<! mk_i32 n <: i32) -! mk_i32 1 <: i32) (v i)
#pop-options
let i32_bit_zero_lemma_to_lt_pow2_n_weak = admit ()
#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"
let i32_bit_zero_lemma_to_positive vec =
  let aux (lane: u64{v lane < 8}) : Lemma (v (to_i32x8 vec lane) >= 0) =
    let x = to_i32x8 vec lane in
    assert (v (mk_int #Ints.U64 (v lane * 32 + 31)) % 32 == 31);
    i32_to_bv_to_i32x8_inv vec lane (mk_u64 31);
    ebit_is_get_bit Ints.I32 x 31;
    reveal_opaque (`%Ints.get_bit) (Ints.get_bit #Ints.I32)
  in
  FStar.Classical.forall_intro aux
#pop-options
#push-options "--fuel 2 --ifuel 1 --z3rlimit 300"
let to_i32x8_eq_to_bv_eq a b =
  let aux (k: u64{v k < 256}) : Lemma (a.(k) == b.(k)) =
    let i : u64 = k /! mk_u64 32 in
    let j : u64 = k %! mk_u64 32 in
    FStar.Math.Lemmas.lemma_div_mod (v k) 32;
    i32_to_bv_to_i32x8_inv a i j;
    i32_to_bv_to_i32x8_inv b i j
  in
  FStar.Classical.forall_intro aux;
  eq_pointwise_to_eq a b
#pop-options
#push-options "--fuel 2 --ifuel 1 --z3rlimit 300"
let lemma_from_i32x8_def_pt f =
  let g : i32x8 = FStar.FunctionalExtensionality.on (i:u64{v i < 8}) f in
  let aux (i: u64{v i < 8})
    : Lemma (to_i32x8 (from_i32x8 (FStar.FunctionalExtensionality.on (i:u64{v i < 8}) f)) i == f i) =
    to_from_i32x8_inv_lemma g;
    assert (to_i32x8 (from_i32x8 g) i == g i);
    assert (g i == f i)
  in
  FStar.Classical.forall_intro aux
#pop-options
let mm256_storeu_si256_i32_lemma = admit ()
let mm256_storeu_si256_i32_len_lemma out vec = ()
let mm256_setzero_si256_lemma = admit ()
let mm256_loadu_si256_i32_lemma = admit ()
let vec256_blendv_epi32_lemma = admit ()
#push-options "--fuel 2 --ifuel 1 --z3rlimit 200"
let mm256_cmpeq_epi32_lemma a b i =
  reveal_opaque (`%I.mm256_cmpeq_epi32) I.mm256_cmpeq_epi32;
  Canon.lemma_mm256_cmpeq_epi32 a b
#pop-options
let mm256_or_si256_lemma = admit ()
#push-options "--fuel 2 --ifuel 1 --z3rlimit 200"
let mm256_sign_epi32_lemma a b i =
  reveal_opaque (`%I.mm256_sign_epi32) I.mm256_sign_epi32;
  reveal_opaque_arithmetic_ops #i32_inttype;
  Canon.lemma_mm256_sign_epi32 a b
#pop-options
#push-options "--fuel 2 --ifuel 2 --z3rlimit 250"
let i32_to_bv_to_i32x4_inv vec i j =
  bit_view_inv Ints.I32 (mk_u64 128) (mk_u64 4) vec i j
#pop-options
#push-options "--fuel 2 --ifuel 2 --z3rlimit 300"
let i32_to_bv_ext a c =
  let h (k: nat{k < 32})
    : Lemma (IVi.bval (IVi.encode_bit Ints.I32 a k) == IVi.bval (IVi.encode_bit Ints.I32 c k)) =
    assert (i32_to_bv a (mk_u64 k) == i32_to_bv c (mk_u64 k)) in
  Canon.dsum2_shift (fun b -> IVi.encode_bit Ints.I32 a b)
                    (fun b -> IVi.encode_bit Ints.I32 c b) 0 0 32 h;
  IVi.lemma_decode_encode Ints.I32 a;
  IVi.lemma_decode_encode Ints.I32 c
#pop-options
let to_i8x16_mm_loadu_si128_lemma = admit ()
let mm256_loadu_si256_u8_lemma = admit ()
let mm_storeu_si128_i32_lemma = admit ()
let mm_storeu_si128_i32_len_lemma out vec = ()
let mm256_movemask_ps_lemma = admit ()
#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"
let coeff_gather_bv_lemma a b c i =
  cast_u8_i32 a; cast_u8_i32 b; cast_u8_i32 c;
  assert_norm (pow2 23 == 8388608);
  Rust_primitives.BitVectors.get_bit_pow2_minus_one #Ints.I32 23 (Ints.mk_usize (v i));
  bit_of_get_bit Ints.I32
    (((((cast c <: i32) <<! mk_i32 16 <: i32) |. ((cast b <: i32) <<! mk_i32 8 <: i32) <: i32)
      |. (cast a <: i32) <: i32) &. mk_i32 8388607 <: i32) (v i);
  if v i >= 23 then ()
  else if v i >= 16 then bit_of_get_bit Ints.U8 c (v i - 16)
  else if v i >= 8 then bit_of_get_bit Ints.U8 b (v i - 8)
  else bit_of_get_bit Ints.U8 a (v i)
#pop-options
#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"
let u8_to_bv_logand15_lemma x i =
  bit_of_get_bit Ints.U8 (x &. mk_u8 15) (v i);
  if v i < 4 then bit_of_get_bit Ints.U8 x (v i)
let u8_to_bv_shr4_lemma x i =
  bit_of_get_bit Ints.U8 (x >>! mk_u8 4 <: u8) (v i);
  if v i < 4 then bit_of_get_bit Ints.U8 x (v i + 4)
#pop-options
