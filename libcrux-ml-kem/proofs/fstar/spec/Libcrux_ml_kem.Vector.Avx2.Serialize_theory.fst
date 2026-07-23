module Libcrux_ml_kem.Vector.Avx2.Serialize_theory
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

(* Hand-written proof theory relocated from src/vector/avx2/serialize.rs
   `hax_lib::fstar::before` blocks (byte-exact raw-string contents, verified
   verbatim against the green extracted module). Consumed only by that module. *)

(* Lane-bound bridge.  Same proof as `vector/avx2.rs`'s before-block helper
   (lemma_vec256_lane_bounded); a local copy lives here because
   `Vector.Avx2.Serialize` is checked before `Vector.Avx2` and so cannot import
   it — but a companion IS checked before both, so the copy is housed here as
   named theory rather than inline. *)
let lemma_vec256_lane_bounded_local
      (vec: Libcrux_intrinsics.Avx2_extract.t_Vec256) (n: nat{n > 0 /\ n <= 16}) (i: nat{i < 16})
    : Lemma
      (requires forall (b: nat{b < 16}). b >= n ==> vec (i * 16 + b) == 0)
      (ensures
        Rust_primitives.BitVectors.bounded
          (Seq.index (Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vec) i) n)
  = let arr = Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 vec in
    let lane = Seq.index arr i in
    let aux (b: usize{v b < 16}) : Lemma (v b > n ==> Rust_primitives.Integers.get_bit lane b == 0)
      = if v b > n then begin
          Libcrux_intrinsics.Avx2_extract.bit_vec_of_int_t_array_vec256_as_i16x16_lemma
            vec 16 (i * 16 + v b);
          FStar.Math.Lemmas.lemma_mod_plus (v b) i 16;
          FStar.Math.Lemmas.lemma_div_plus (v b) i 16
        end
        else ()
    in
    Classical.forall_intro aux;
    Rust_primitives.BitVectors.lemma_get_bit_bounded' lane n
