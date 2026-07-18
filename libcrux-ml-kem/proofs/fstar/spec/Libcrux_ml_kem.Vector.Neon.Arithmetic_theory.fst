module Libcrux_ml_kem.Vector.Neon.Arithmetic_theory
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

(* Hand-written proof theory relocated from src/vector/neon/arithmetic.rs
   `hax_lib::fstar::before` blocks (byte-exact raw-string contents, verified verbatim
   against the green extracted module). Consumed only by that module. *)

let lemma_neon_floor_collapse (p: int)
    : Lemma ((p / pow2 15 + pow2 10) / pow2 11 == (p / pow2 16 + pow2 9) / pow2 10) =
  FStar.Math.Lemmas.pow2_plus 10 15;
  FStar.Math.Lemmas.division_addition_lemma p (pow2 15) (pow2 10);
  FStar.Math.Lemmas.pow2_plus 15 11;
  FStar.Math.Lemmas.division_multiplication_lemma (p + pow2 25) (pow2 15) (pow2 11);
  FStar.Math.Lemmas.pow2_plus 9 16;
  FStar.Math.Lemmas.division_addition_lemma p (pow2 16) (pow2 9);
  FStar.Math.Lemmas.pow2_plus 16 10;
  FStar.Math.Lemmas.division_multiplication_lemma (p + pow2 25) (pow2 16) (pow2 10)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"

(* The Neon barrett lane chain (saturating doubling-mul-high + add 1024 + >>11)
   collapses to the scalar `Spec.Utils.barrett_red`: both quotients equal
   floor((x*20159 + 2^25) / 2^26). *)
let lemma_barrett_lane_eq (x: i16)
    : Lemma (requires Spec.Utils.is_i16b 28296 x)
      (ensures
        (let prod:i32 = ((cast x <: i32) *. (cast (mk_i16 20159) <: i32)) >>! (mk_i32 15) in
          let vec1:i16 =
            (if prod >. mk_i32 32767
              then mk_i16 32767
              else if prod <. mk_i32 (- 32768) then mk_i16 (- 32768) else (cast prod <: i16))
          in
          x -. (((vec1 +. mk_i16 1024) >>! (mk_i32 11)) *. mk_i16 3329) == Spec.Utils.barrett_red x)) =
  let xx:int = v x in
  assert (xx * 20159 <= 570419064 /\ xx * 20159 >= -570419064);
  let prod:i32 = ((cast x <: i32) *. (cast (mk_i16 20159) <: i32)) >>! (mk_i32 15) in
  assert (v prod == (xx * 20159) / pow2 15);
  FStar.Math.Lemmas.lemma_div_le (xx * 20159) 570419064 (pow2 15);
  FStar.Math.Lemmas.lemma_div_le (-570419064) (xx * 20159) (pow2 15);
  assert_norm (570419064 / pow2 15 == 17407);
  assert_norm ((-570419064) / pow2 15 == -17408);
  let vec1:i16 = (cast prod <: i16) in
  let vec2:i16 = vec1 +. mk_i16 1024 in
  let quotient:i16 = vec2 >>! (mk_i32 11) in
  lemma_neon_floor_collapse (xx * 20159);
  assert_norm (pow2 10 == 1024);
  assert_norm (pow2 9 == 512);
  assert (v quotient == ((xx * 20159) / pow2 16 + 512) / pow2 10);
  ()
#pop-options

#push-options "--z3rlimit 200"
(* The unsigned multiply-by-62209 detour reinterprets to a signed
   multiply-by-(-3327), since 62209 == -3327 (mod 2^16). *)
let lemma_u16_detour (a: i16)
    : Lemma
      (Rust_primitives.Integers.cast_mod #Rust_primitives.Integers.u16_inttype
          #Rust_primitives.Integers.i16_inttype
          ((Rust_primitives.Integers.cast_mod #Rust_primitives.Integers.i16_inttype
                #Rust_primitives.Integers.u16_inttype
                a) *.
            mk_u16 62209) ==
        a *. (mk_i16 (-3327))) =
  let aa = v a in
  FStar.Math.Lemmas.lemma_mod_mul_distr_l aa 62209 (pow2 16);
  FStar.Math.Lemmas.lemma_mod_plus (aa * (-3327)) aa (pow2 16);
  assert (aa * 62209 == aa * (-3327) + aa * pow2 16);
  assert (((aa % pow2 16) * 62209) % pow2 16 == (aa * (-3327)) % pow2 16);
  ()
#pop-options

#push-options "--z3rlimit 300"
(* The saturating doubling-mul-high `e_vqdmulhq_n_s16 m d` (model `(m*d)>>15`)
   then `>>1` equals the scalar high half `(m*d)>>16`, for products below 2^28
   (so no saturation and the i16 cast is exact). *)
let lemma_qdmulh_shift1 (m d: i16)
    : Lemma (requires Spec.Utils.is_intb (pow2 28) (v m * v d))
      (ensures
        (let prod:i32 = ((cast m <: i32) *. (cast d <: i32)) >>! (mk_i32 15) in
          let sat:i16 =
            (if prod >. mk_i32 32767
              then mk_i16 32767
              else if prod <. mk_i32 (- 32768) then mk_i16 (- 32768) else (cast prod <: i16))
          in
          (sat >>! (mk_i32 1)) ==
          (cast (((cast m <: i32) *. (cast d <: i32)) >>! (mk_i32 16)) <: i16))) =
  let p:int = v m * v d in
  assert (v ((cast m <: i32) *. (cast d <: i32)) == p);
  let prod:i32 = ((cast m <: i32) *. (cast d <: i32)) >>! (mk_i32 15) in
  assert (v prod == p / pow2 15);
  FStar.Math.Lemmas.lemma_div_le p (pow2 28) (pow2 15);
  FStar.Math.Lemmas.lemma_div_le (- pow2 28) p (pow2 15);
  assert_norm (pow2 28 / pow2 15 == pow2 13);
  assert_norm ((- pow2 28) / pow2 15 == - pow2 13);
  assert_norm (pow2 13 < 32767);
  let sat:i16 = (cast prod <: i16) in
  assert (v (sat >>! (mk_i32 1)) == (p / pow2 15) / pow2 1);
  FStar.Math.Lemmas.division_multiplication_lemma p (pow2 15) (pow2 1);
  FStar.Math.Lemmas.pow2_plus 15 1;
  ()
#pop-options
