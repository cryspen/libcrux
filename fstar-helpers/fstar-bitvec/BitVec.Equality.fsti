module BitVec.Equality

open Core
open Rust_primitives
open FStar.Mul
open FStar.FunctionalExtensionality

val bv_equality #n (bv1 bv2: bit_vec n): bool
val rewrite n (bv1: bit_vec n): Lemma (bv_equality #n bv1 bv1 == true)
