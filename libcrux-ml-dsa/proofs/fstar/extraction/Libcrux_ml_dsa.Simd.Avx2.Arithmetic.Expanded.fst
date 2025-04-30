module Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Hello
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

unfold let i32_to_i64 (x: i32): i64 = Rust_primitives.cast x
unfold let i64_to_i32 (x: i64): i32 = Rust_primitives.cast x

unfold type i32x8 = Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32

unfold let i32x8_of_bv (bv: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)): i32x8 =
  Core.Convert.f_from bv
unfold let bv_of_i32x8 (bv: i32x8): Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_from bv

let cast_lemma1 x: Lemma (Rust_primitives.cast x == i32_to_i64 x) = ()
let cast_lemma2 x: Lemma (Rust_primitives.cast x == i64_to_i32 x) = ()
let cast_lemma3 x n: Lemma ((Core.Convert.f_from x <: i32x8) n == i32x8_of_bv x n) = ()
let cast_lemma4 x: Lemma (Core.Convert.f_from x == bv_of_i32x8 x) = ()

let expanded (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) = 
        bv_of_i32x8 (FStar.FunctionalExtensionality.on_domain
              (i:
                Rust_primitives.Integers.u64
                  { Rust_primitives.Integers.v i <
                    Rust_primitives.Integers.v (Rust_primitives.Integers.mk_u64 8) })
              (fun i ->
                  match i with
                  | Rust_primitives.Integers.MkInt 0 ->
                    Core.Num.impl_i32__wrapping_sub (i64_to_i32
                          (i32_to_i64 (i32x8_of_bv
                                  lhs
                                  (Rust_primitives.Integers.mk_u64 0)) *!
                            i32_to_i64 (i32x8_of_bv
                                  rhs
                                  (Rust_primitives.Integers.mk_u64 0)) >>!
                            Rust_primitives.Integers.mk_i32 32))
                      (i64_to_i32 (i32_to_i64
                              (i64_to_i32 (i32_to_i64
                                      (i64_to_i32 (i32_to_i64
                                              (i32x8_of_bv
                                                  lhs
                                                  (Rust_primitives.Integers.mk_u64 0)) *!
                                            i32_to_i64 (i32x8_of_bv
                                                  rhs
                                                  (Rust_primitives.Integers.mk_u64 0)))) *!
                                    i32_to_i64 (Rust_primitives.cast
                                          Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                                        ))) *!
                            i32_to_i64 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
                             >>!
                            Rust_primitives.Integers.mk_i32 32))
                  | Rust_primitives.Integers.MkInt 1 ->
                    Core.Num.impl_i32__wrapping_sub (i64_to_i32
                          (i32_to_i64 (i32x8_of_bv
                                  lhs
                                  (Rust_primitives.Integers.mk_u64 1)) *!
                            i32_to_i64 (i32x8_of_bv
                                  rhs
                                  (Rust_primitives.Integers.mk_u64 1)) >>!
                            Rust_primitives.Integers.mk_i32 32))
                      (i64_to_i32 (i32_to_i64
                              (i64_to_i32 (i32_to_i64
                                      (i64_to_i32 (i32_to_i64
                                              (i32x8_of_bv
                                                  lhs
                                                  (Rust_primitives.Integers.mk_u64 1)) *!
                                            i32_to_i64 (i32x8_of_bv
                                                  rhs
                                                  (Rust_primitives.Integers.mk_u64 1)))) *!
                                    i32_to_i64 (Rust_primitives.cast
                                          Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                                        ))) *!
                            i32_to_i64 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
                             >>!
                            Rust_primitives.Integers.mk_i32 32))
                  | Rust_primitives.Integers.MkInt 2 ->
                    Core.Num.impl_i32__wrapping_sub (i64_to_i32
                          (i32_to_i64 (i32x8_of_bv
                                  lhs
                                  (Rust_primitives.Integers.mk_u64 2)) *!
                            i32_to_i64 (i32x8_of_bv
                                  rhs
                                  (Rust_primitives.Integers.mk_u64 2)) >>!
                            Rust_primitives.Integers.mk_i32 32))
                      (i64_to_i32 (i32_to_i64
                              (i64_to_i32 (i32_to_i64
                                      (i64_to_i32 (i32_to_i64
                                              (i32x8_of_bv
                                                  lhs
                                                  (Rust_primitives.Integers.mk_u64 2)) *!
                                            i32_to_i64 (i32x8_of_bv
                                                  rhs
                                                  (Rust_primitives.Integers.mk_u64 2)))) *!
                                    i32_to_i64 (Rust_primitives.cast
                                          Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                                        ))) *!
                            i32_to_i64 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
                             >>!
                            Rust_primitives.Integers.mk_i32 32))
                  | Rust_primitives.Integers.MkInt 3 ->
                    Core.Num.impl_i32__wrapping_sub (i64_to_i32
                          (i32_to_i64 (i32x8_of_bv
                                  lhs
                                  (Rust_primitives.Integers.mk_u64 3)) *!
                            i32_to_i64 (i32x8_of_bv
                                  rhs
                                  (Rust_primitives.Integers.mk_u64 3)) >>!
                            Rust_primitives.Integers.mk_i32 32))
                      (i64_to_i32 (i32_to_i64
                              (i64_to_i32 (i32_to_i64
                                      (i64_to_i32 (i32_to_i64
                                              (i32x8_of_bv
                                                  lhs
                                                  (Rust_primitives.Integers.mk_u64 3)) *!
                                            i32_to_i64 (i32x8_of_bv
                                                  rhs
                                                  (Rust_primitives.Integers.mk_u64 3)))) *!
                                    i32_to_i64 (Rust_primitives.cast
                                          Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                                        ))) *!
                            i32_to_i64 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
                             >>!
                            Rust_primitives.Integers.mk_i32 32))
                  | Rust_primitives.Integers.MkInt 4 ->
                    Core.Num.impl_i32__wrapping_sub (i64_to_i32
                          (i32_to_i64 (i32x8_of_bv
                                  lhs
                                  (Rust_primitives.Integers.mk_u64 4)) *!
                            i32_to_i64 (i32x8_of_bv
                                  rhs
                                  (Rust_primitives.Integers.mk_u64 4)) >>!
                            Rust_primitives.Integers.mk_i32 32))
                      (i64_to_i32 (i32_to_i64
                              (i64_to_i32 (i32_to_i64
                                      (i64_to_i32 (i32_to_i64
                                              (i32x8_of_bv
                                                  lhs
                                                  (Rust_primitives.Integers.mk_u64 4)) *!
                                            i32_to_i64 (i32x8_of_bv
                                                  rhs
                                                  (Rust_primitives.Integers.mk_u64 4)))) *!
                                    i32_to_i64 (Rust_primitives.cast
                                          Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                                        ))) *!
                            i32_to_i64 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
                             >>!
                            Rust_primitives.Integers.mk_i32 32))
                  | Rust_primitives.Integers.MkInt 5 ->
                    Core.Num.impl_i32__wrapping_sub (i64_to_i32
                          (i32_to_i64 (i32x8_of_bv
                                  lhs
                                  (Rust_primitives.Integers.mk_u64 5)) *!
                            i32_to_i64 (i32x8_of_bv
                                  rhs
                                  (Rust_primitives.Integers.mk_u64 5)) >>!
                            Rust_primitives.Integers.mk_i32 32))
                      (i64_to_i32 (i32_to_i64
                              (i64_to_i32 (i32_to_i64
                                      (i64_to_i32 (i32_to_i64
                                              (i32x8_of_bv
                                                  lhs
                                                  (Rust_primitives.Integers.mk_u64 5)) *!
                                            i32_to_i64 (i32x8_of_bv
                                                  rhs
                                                  (Rust_primitives.Integers.mk_u64 5)))) *!
                                    i32_to_i64 (Rust_primitives.cast
                                          Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                                        ))) *!
                            i32_to_i64 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
                             >>!
                            Rust_primitives.Integers.mk_i32 32))
                  | Rust_primitives.Integers.MkInt 6 ->
                    Core.Num.impl_i32__wrapping_sub (i64_to_i32
                          (i32_to_i64 (i32x8_of_bv
                                  lhs
                                  (Rust_primitives.Integers.mk_u64 6)) *!
                            i32_to_i64 (i32x8_of_bv
                                  rhs
                                  (Rust_primitives.Integers.mk_u64 6)) >>!
                            Rust_primitives.Integers.mk_i32 32))
                      (i64_to_i32 (i32_to_i64
                              (i64_to_i32 (i32_to_i64
                                      (i64_to_i32 (i32_to_i64
                                              (i32x8_of_bv
                                                  lhs
                                                  (Rust_primitives.Integers.mk_u64 6)) *!
                                            i32_to_i64 (i32x8_of_bv
                                                  rhs
                                                  (Rust_primitives.Integers.mk_u64 6)))) *!
                                    i32_to_i64 (Rust_primitives.cast
                                          Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                                        ))) *!
                            i32_to_i64 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
                             >>!
                            Rust_primitives.Integers.mk_i32 32))
                  | Rust_primitives.Integers.MkInt 7 ->
                    Core.Num.impl_i32__wrapping_sub (i64_to_i32
                          (i32_to_i64 (i32x8_of_bv
                                  lhs
                                  (Rust_primitives.Integers.mk_u64 7)) *!
                            i32_to_i64 (i32x8_of_bv
                                  rhs
                                  (Rust_primitives.Integers.mk_u64 7)) >>!
                            Rust_primitives.Integers.mk_i32 32))
                      (i64_to_i32 (i32_to_i64
                              (i64_to_i32 (i32_to_i64
                                      (i64_to_i32 (i32_to_i64
                                              (i32x8_of_bv
                                                  lhs
                                                  (Rust_primitives.Integers.mk_u64 7)) *!
                                            i32_to_i64 (i32x8_of_bv
                                                  rhs
                                                  (Rust_primitives.Integers.mk_u64 7)))) *!
                                    i32_to_i64 (Rust_primitives.cast
                                          Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                                        ))) *!
                            i32_to_i64 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
                             >>!
                            Rust_primitives.Integers.mk_i32 32))
                  | _ ->
                    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"
                        )))

open FStar.Tactics

let expanded_lemma (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Lemma (expanded lhs rhs == Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply lhs rhs) = 
    assert (expanded lhs rhs == Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply lhs rhs) by (
      compute ();
      trefl ()
    )



// [@@FStar.Tactics.postprocess_with (fun _ -> 
//         let open FStar.Tactics in
//         norm [iota; primops; delta_only [`% Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply ]; zeta];
//         l_to_r [`cast_lemma1;`cast_lemma2;`cast_lemma3;`cast_lemma4];
//         dump "show";
//         trefl ()
//     )]

// let f (lhs rhs: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
//     : Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
//   let lhs:Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
//     Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply lhs rhs
//   in
//   lhs
