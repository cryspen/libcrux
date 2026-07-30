module Libcrux_ml_kem.Vector.Avx2.Unpack_theory
#set-options "--fuel 0 --ifuel 1 --z3rlimit 50"
open FStar.Mul
open Core_models
open Libcrux_intrinsics.Avx2
open Libcrux_intrinsics.Avx2_ml_kem_views

module RI = Rust_primitives.Integers

(* ============================================================================
   DESERIALIZE unpack spine — the `set_epi16 (duplicated bytes)` -> `mullo by
   2^k` -> `srli` -> `and mask` shape shared by the AVX2 deserialize widths.

   Structured per the session-7 keystone lesson: the PURE i16/u16 BIT ARITHMETIC
   (`lemma_mul_pow2_bit`, `lemma_srli4_and15_bits`, `lemma_deser4_lane`) is
   proven with no vector terms in scope; the lane view only appears in the final
   16-arm ground dispatch, whose arms do nothing but pin two literal lane values
   and call the arithmetic lemma.
   ========================================================================== *)

(* ── pure bit arithmetic ──────────────────────────────────────────────────── *)

(* Generalisation of the companion's `lemma_mul_pow2_bit15` to an arbitrary bit
   position: multiplying by (2^k mod 2^16) moves bit n-k of x to bit n. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 400"
let lemma_mul_pow2_bit (x m: i16) (k: nat) (n: nat{k <= n /\ n <= 15})
  : Lemma (requires (v m) % pow2 16 == pow2 k)
          (ensures RI.get_bit (RI.mul_mod x m) (sz n) == RI.get_bit x (sz (n - k))) =
  let y: i16 = RI.mul_mod x m in
  let n16 = pow2 16 in
  assert_norm (pow2 16 == 65536);
  reveal_opaque (`%RI.get_bit) (RI.get_bit #RI.I16);
  let x16 = (v x) % n16 in
  let y16 = (v y) % n16 in
  assert ((v y) % n16 == (v x * v m) % n16);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v x) (v m) n16;
  FStar.Math.Lemmas.lemma_mod_mul_distr_l (v x) (pow2 k) n16;
  assert (y16 == (x16 * pow2 k) % n16);
  FStar.Math.Lemmas.pow2_modulo_division_lemma_1 (x16 * pow2 k) n 16;
  FStar.Math.Lemmas.pow2_plus k (n - k);
  FStar.Math.Lemmas.division_multiplication_lemma (x16 * pow2 k) (pow2 k) (pow2 (n - k));
  FStar.Math.Lemmas.cancel_mul_div x16 (pow2 k);
  FStar.Math.Lemmas.modulo_modulo_lemma ((x16 * pow2 k) / pow2 n) 2 (pow2 0);
  assert ((y16 / pow2 n) % 2 == (x16 / pow2 (n - k)) % 2)
#pop-options

(* bit c of the low-nibble mask constant. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"
let lemma_bit_of_15 (c: nat{c < 16})
  : Lemma (RI.get_bit (mk_i16 15) (sz c) == (if c < 4 then 1 else 0)) =
  reveal_opaque (`%RI.get_bit) (RI.get_bit #RI.I16);
  assert_norm (pow2 16 == 65536);
  if c < 4 then begin
    assert_norm (pow2 0 == 1); assert_norm (pow2 1 == 2);
    assert_norm (pow2 2 == 4); assert_norm (pow2 3 == 8);
    assert (c == 0 \/ c == 1 \/ c == 2 \/ c == 3)
  end
  else begin
    assert_norm (pow2 4 == 16);
    FStar.Math.Lemmas.pow2_le_compat c 4;
    FStar.Math.Lemmas.small_division_lemma_1 15 (pow2 c)
  end
#pop-options

(* the nibble extract: `(y >>u 4) & 15` keeps bits 4..7 of y in positions 0..3. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 400"
let lemma_srli4_and15_bits (y: i16) (c: nat{c < 16})
  : Lemma (RI.get_bit ((cast ((cast y <: u16) >>! mk_i32 4 <: u16) <: i16) &. mk_i16 15) (sz c) ==
           (if c < 4 then RI.get_bit y (sz (4 + c)) else 0)) =
  assert_norm (pow2 4 == 16); assert_norm (pow2 16 == 65536);
  reveal_opaque (`%RI.get_bit) (RI.get_bit #RI.I16);
  reveal_opaque (`%RI.get_bit) (RI.get_bit #RI.U16);
  let yu: u16 = cast y <: u16 in
  let sh: u16 = yu >>! mk_i32 4 in
  assert (v yu == (v y) % pow2 16);
  assert (v sh == (v yu) / pow2 4);
  let r: i16 = cast sh <: i16 in
  assert (v r == v sh);
  lemma_bit_of_15 c;
  RI.get_bit_and r (mk_i16 15) (sz c);
  if c < 4 then begin
    FStar.Math.Lemmas.pow2_plus 4 c;
    FStar.Math.Lemmas.division_multiplication_lemma (v yu) (pow2 4) (pow2 c);
    FStar.Math.Lemmas.small_mod (v r) (pow2 16)
  end
#pop-options

(* one lane: source byte `x`, multiplier `m == 2^k` with k in {0,4}.  Bit c of
   the unpacked lane is bit (4 - k + c) of the source byte, for c < 4. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 400"
let lemma_deser4_lane (x m: i16) (k: nat{k == 0 \/ k == 4}) (c: nat{c < 16})
  : Lemma (requires (v m) % pow2 16 == pow2 k)
          (ensures
            RI.get_bit ((cast ((cast (RI.mul_mod x m) <: u16) >>! mk_i32 4 <: u16) <: i16)
                        &. mk_i16 15) (sz c) ==
            (if c < 4 then RI.get_bit x (sz (4 - k + c)) else 0)) =
  lemma_srli4_and15_bits (RI.mul_mod x m) c;
  if c < 4 then lemma_mul_pow2_bit x m k (4 + c)
#pop-options

(* the two multiplier constants, as ground pow2 images. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"
let lemma_deser4_mults ()
  : Lemma ((v ((mk_i16 1 <<! mk_i32 0 <: i16) <: i16)) % pow2 16 == pow2 0 /\
           (v ((mk_i16 1 <<! mk_i32 4 <: i16) <: i16)) % pow2 16 == pow2 4 /\
           ((mk_i16 1 <<! mk_i32 4 <: i16) -! mk_i16 1 <: i16) == mk_i16 15) =
  assert_norm (pow2 0 == 1); assert_norm (pow2 4 == 16); assert_norm (pow2 16 == 65536)
#pop-options

(* ── the per-index deserialize_4 bit obligation ───────────────────────────────
   Mirror of the companion's `lemma_deserialize_1_bits` at width 4.  The lane
   view appears ONLY here; each of the 16 arms pins two literal lane values and
   calls `lemma_deser4_lane`, which carries all of the bit arithmetic. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 400 --split_queries always"
let lemma_deserialize_4_bits (b0 b1 b2 b3 b4 b5 b6 b7: i16) (i: nat{i < 256})
  : Lemma
      (let coeff = mm256_set_epi16 b7 b7 b6 b6 b5 b5 b4 b4 b3 b3 b2 b2 b1 b1 b0 b0 in
       let mults = mm256_set_epi16 (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) in
       let r = mm256_and_si256 (mm256_srli_epi16 (mk_i32 4) (mm256_mullo_epi16 coeff mults))
                 (mm256_set1_epi16 ((mk_i16 1 <<! mk_i32 4 <: i16) -! mk_i16 1 <: i16)) in
       bv_bit r i = (if i % 16 < 4
                     then (let j = (i / 16) * 4 + i % 16 in
                           match i / 32 with
                           | 0 -> RI.get_bit b0 (sz j)
                           | 1 -> RI.get_bit b1 (sz (j - 8))
                           | 2 -> RI.get_bit b2 (sz (j - 16))
                           | 3 -> RI.get_bit b3 (sz (j - 24))
                           | 4 -> RI.get_bit b4 (sz (j - 32))
                           | 5 -> RI.get_bit b5 (sz (j - 40))
                           | 6 -> RI.get_bit b6 (sz (j - 48))
                           | 7 -> RI.get_bit b7 (sz (j - 56)))
                     else 0)) =
  let coeff = mm256_set_epi16 b7 b7 b6 b6 b5 b5 b4 b4 b3 b3 b2 b2 b1 b1 b0 b0 in
  let mults = mm256_set_epi16 (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) in
  let msb = mm256_mullo_epi16 coeff mults in
  let lsb = mm256_srli_epi16 (mk_i32 4) msb in
  let mask = mm256_set1_epi16 ((mk_i16 1 <<! mk_i32 4 <: i16) -! mk_i16 1 <: i16) in
  let r = mm256_and_si256 lsb mask in
  let l = i / 16 in
  let bb = i % 16 in
  lemma_deser4_mults ();
  lemma_mm256_set_epi16_lanes b7 b7 b6 b6 b5 b5 b4 b4 b3 b3 b2 b2 b1 b1 b0 b0;
  lemma_mm256_set_epi16_lanes (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16);
  lemma_mm256_set1_epi16 ((mk_i16 1 <<! mk_i32 4 <: i16) -! mk_i16 1 <: i16);
  bit_vec_of_int_t_array_vec256_as_i16x16_lemma r 16 i;
  assert (get_lane msb l == RI.mul_mod (get_lane coeff l) (get_lane mults l));
  assert (get_lane lsb l ==
          (cast ((cast (get_lane msb l) <: u16) >>! mk_i32 4 <: u16) <: i16));
  assert (get_lane mask l == mk_i16 15);
  assert (get_lane r l == (get_lane lsb l &. get_lane mask l));
  (if false then ()
   else if l = 0 then begin
     assert (get_lane coeff 0 == b0);
     assert (get_lane mults 0 == (mk_i16 1 <<! mk_i32 4 <: i16));
     lemma_deser4_lane b0 (mk_i16 1 <<! mk_i32 4 <: i16) 4 bb
   end
   else if l = 1 then begin
     assert (get_lane coeff 1 == b0);
     assert (get_lane mults 1 == (mk_i16 1 <<! mk_i32 0 <: i16));
     lemma_deser4_lane b0 (mk_i16 1 <<! mk_i32 0 <: i16) 0 bb
   end
   else if l = 2 then begin
     assert (get_lane coeff 2 == b1);
     assert (get_lane mults 2 == (mk_i16 1 <<! mk_i32 4 <: i16));
     lemma_deser4_lane b1 (mk_i16 1 <<! mk_i32 4 <: i16) 4 bb
   end
   else if l = 3 then begin
     assert (get_lane coeff 3 == b1);
     assert (get_lane mults 3 == (mk_i16 1 <<! mk_i32 0 <: i16));
     lemma_deser4_lane b1 (mk_i16 1 <<! mk_i32 0 <: i16) 0 bb
   end
   else if l = 4 then begin
     assert (get_lane coeff 4 == b2);
     assert (get_lane mults 4 == (mk_i16 1 <<! mk_i32 4 <: i16));
     lemma_deser4_lane b2 (mk_i16 1 <<! mk_i32 4 <: i16) 4 bb
   end
   else if l = 5 then begin
     assert (get_lane coeff 5 == b2);
     assert (get_lane mults 5 == (mk_i16 1 <<! mk_i32 0 <: i16));
     lemma_deser4_lane b2 (mk_i16 1 <<! mk_i32 0 <: i16) 0 bb
   end
   else if l = 6 then begin
     assert (get_lane coeff 6 == b3);
     assert (get_lane mults 6 == (mk_i16 1 <<! mk_i32 4 <: i16));
     lemma_deser4_lane b3 (mk_i16 1 <<! mk_i32 4 <: i16) 4 bb
   end
   else if l = 7 then begin
     assert (get_lane coeff 7 == b3);
     assert (get_lane mults 7 == (mk_i16 1 <<! mk_i32 0 <: i16));
     lemma_deser4_lane b3 (mk_i16 1 <<! mk_i32 0 <: i16) 0 bb
   end
   else if l = 8 then begin
     assert (get_lane coeff 8 == b4);
     assert (get_lane mults 8 == (mk_i16 1 <<! mk_i32 4 <: i16));
     lemma_deser4_lane b4 (mk_i16 1 <<! mk_i32 4 <: i16) 4 bb
   end
   else if l = 9 then begin
     assert (get_lane coeff 9 == b4);
     assert (get_lane mults 9 == (mk_i16 1 <<! mk_i32 0 <: i16));
     lemma_deser4_lane b4 (mk_i16 1 <<! mk_i32 0 <: i16) 0 bb
   end
   else if l = 10 then begin
     assert (get_lane coeff 10 == b5);
     assert (get_lane mults 10 == (mk_i16 1 <<! mk_i32 4 <: i16));
     lemma_deser4_lane b5 (mk_i16 1 <<! mk_i32 4 <: i16) 4 bb
   end
   else if l = 11 then begin
     assert (get_lane coeff 11 == b5);
     assert (get_lane mults 11 == (mk_i16 1 <<! mk_i32 0 <: i16));
     lemma_deser4_lane b5 (mk_i16 1 <<! mk_i32 0 <: i16) 0 bb
   end
   else if l = 12 then begin
     assert (get_lane coeff 12 == b6);
     assert (get_lane mults 12 == (mk_i16 1 <<! mk_i32 4 <: i16));
     lemma_deser4_lane b6 (mk_i16 1 <<! mk_i32 4 <: i16) 4 bb
   end
   else if l = 13 then begin
     assert (get_lane coeff 13 == b6);
     assert (get_lane mults 13 == (mk_i16 1 <<! mk_i32 0 <: i16));
     lemma_deser4_lane b6 (mk_i16 1 <<! mk_i32 0 <: i16) 0 bb
   end
   else if l = 14 then begin
     assert (get_lane coeff 14 == b7);
     assert (get_lane mults 14 == (mk_i16 1 <<! mk_i32 4 <: i16));
     lemma_deser4_lane b7 (mk_i16 1 <<! mk_i32 4 <: i16) 4 bb
   end
   else if l = 15 then begin
     assert (get_lane coeff 15 == b7);
     assert (get_lane mults 15 == (mk_i16 1 <<! mk_i32 0 <: i16));
     lemma_deser4_lane b7 (mk_i16 1 <<! mk_i32 0 <: i16) 0 bb
   end
   else ());
  assert (l < 16)
#pop-options
