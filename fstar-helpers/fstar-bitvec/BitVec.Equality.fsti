module BitVec.Equality

open Core_models
open Rust_primitives
open FStar.Mul
open FStar.FunctionalExtensionality

val bv_equality #n (bv1 bv2: bit_vec n): bool
val bv_equality_elim #n (bv1 bv2: bit_vec n)
  : Lemma (requires bv_equality bv1 bv2)
          (ensures  bv1 == bv2)
val bv_equality_intro #n (bv1 bv2: bit_vec n)
  : Lemma (requires bv1 == bv2)
          (ensures  bv_equality bv1 bv2)
val rewrite n (bv1: bit_vec n): Lemma (bv_equality #n bv1 bv1 == true)


