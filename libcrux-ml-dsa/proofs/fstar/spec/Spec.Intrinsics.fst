module Spec.Intrinsics
open Core
open Core_models.Core_arch.X86.Interpretations.Int_vec

open FStar.FunctionalExtensionality
type t_FunArray (n: u64) t = i:u64 {v i < v n} ^-> t

let i32x4 = t_FunArray (mk_u64 4) i32
let bv128 = Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

let i32x8 = t_FunArray (mk_u64 8) i32
let i64x4 = t_FunArray (mk_u64 4) i64
let bv256 = Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

assume val to_i32x8 (x:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)): i32x8
assume val to_i32x4 (x: bv128): i32x4
assume val from_i32x8 (x:i32x8): Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
assume val to_from_i32x8_lemma (x:i32x8):
  Lemma (to_i32x8 (from_i32x8 x) == x) [SMTPat (to_i32x8 (from_i32x8 x))]

let mm256_shuffle_epi32_index (a:i32) (i:u64{v i<4}) : u64 =
  cast ((a >>! (i *! mk_u64 2 <: u64) <: i32) %! mk_i32 4 <: i32) <: u64

assume val mm256_shuffle_epi32_lemma (a:i32) (b:bv256) (i:u64{v i < 8}):
  Lemma (to_i32x8 (Libcrux_intrinsics.Avx2.mm256_shuffle_epi32 a b) i ==
       (if i <. mk_u64 4 <: bool
        then (to_i32x8 b (mm256_shuffle_epi32_index a i))
        else (to_i32x8 b (mk_u64 4 +! mm256_shuffle_epi32_index a (i -! mk_u64 4)))))
        [SMTPat (to_i32x8 (Libcrux_intrinsics.Avx2.mm256_shuffle_epi32 a b) i)]

assume val mm256_sub_epi32_lemma (a b: bv256) (i:u64{v i < 8}):
  Lemma (to_i32x8 (Libcrux_intrinsics.Avx2.mm256_sub_epi32 a b) i ==
         sub_mod (to_i32x8 a i) (to_i32x8 b i))
         [SMTPat (to_i32x8 (Libcrux_intrinsics.Avx2.mm256_sub_epi32 a b) i)]

assume val mm256_add_epi32_lemma (a b: bv256) (i:u64{v i < 8}):
  Lemma (to_i32x8 (Libcrux_intrinsics.Avx2.mm256_add_epi32 a b) i ==
         add_mod (to_i32x8 a i) (to_i32x8 b i))
         [SMTPat (to_i32x8 (Libcrux_intrinsics.Avx2.mm256_add_epi32 a b) i)]

assume val mm256_mul_epi32_lemma (a b: bv256) (i:u64{v i < 8}):
  Lemma (to_i32x8 (Libcrux_intrinsics.Avx2.mm256_mul_epi32 a b) i ==
         (
           let j = i /! mk_int 2 in
           let v64 = (cast (to_i32x8 a j) <: i64) *! (cast (to_i32x8 b j) <: i64) in
           if v i % 2 = 0 then cast (v64 >>! mk_u64 4) else cast v64
         ))
         [SMTPat (to_i32x8 (Libcrux_intrinsics.Avx2.mm256_mul_epi32 a b) i)]

assume val mm256_set_epi32_lemma (x0 x1 x2 x3 x4 x5 x6 x7:i32) (i:u64{v i < 8}):
  Lemma (to_i32x8 (Libcrux_intrinsics.Avx2.mm256_set_epi32 x0 x1 x2 x3 x4 x5 x6 x7) i ==
        (match i <: u64 with
        | Rust_primitives.Integers.MkInt 0 -> x7
        | Rust_primitives.Integers.MkInt 1 -> x6
        | Rust_primitives.Integers.MkInt 2 -> x5
        | Rust_primitives.Integers.MkInt 3 -> x4
        | Rust_primitives.Integers.MkInt 4 -> x3
        | Rust_primitives.Integers.MkInt 5 -> x2
        | Rust_primitives.Integers.MkInt 6 -> x1
        | Rust_primitives.Integers.MkInt 7 -> x0
        | _ ->
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

              <:
              Rust_primitives.Hax.t_Never)
          <:
          i32))
  [SMTPat (to_i32x8 (Libcrux_intrinsics.Avx2.mm256_set_epi32 x0 x1 x2 x3 x4 x5 x6 x7) i)]

assume val mm256_blend_epi32_lemma (imm8: i32) (a b: bv256) (i:u64{v i < 8}):
  Lemma (to_i32x8 (Libcrux_intrinsics.Avx2.mm256_blend_epi32 imm8 a b) i ==
        (if ((imm8 >>! i <: i32) %! mk_i32 2 <: i32) =. mk_i32 0 <: bool
         then to_i32x8 a i
         else to_i32x8 b i))

assume val mm256_set_m128i_lemma (hi lo: bv128) (i:u64{v i < 8}):
  Lemma (to_i32x8 (Libcrux_intrinsics.Avx2.mm256_set_m128i hi lo) i ==
        (match i <: u64 with
        | Rust_primitives.Integers.MkInt 0 -> to_i32x4 lo (mk_u64 0)
        | Rust_primitives.Integers.MkInt 1 -> to_i32x4 lo (mk_u64 1)
        | Rust_primitives.Integers.MkInt 2 -> to_i32x4 lo (mk_u64 2)
        | Rust_primitives.Integers.MkInt 3 -> to_i32x4 lo (mk_u64 3)
        | Rust_primitives.Integers.MkInt 4 -> to_i32x4 hi (mk_u64 0)
        | Rust_primitives.Integers.MkInt 5 -> to_i32x4 hi (mk_u64 1)
        | Rust_primitives.Integers.MkInt 6 -> to_i32x4 hi (mk_u64 2)
        | Rust_primitives.Integers.MkInt 7 -> to_i32x4 hi (mk_u64 3)
        | _ ->
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

              <:
              Rust_primitives.Hax.t_Never)
          <:
          i32))
  [SMTPat (to_i32x8 (Libcrux_intrinsics.Avx2.mm256_set_m128i hi lo) i)]

assume val mm256_permute2x128_si256_lemma_i32x4 (imm8: i32) (a b: bv256) (j:u64{v j < 8}):
  Lemma (to_i32x8 (Libcrux_intrinsics.Avx2.mm256_permute2x128_si256 imm8 a b) j ==
        (
          let i:u64 = j /! mk_int 4 in
          let offset = v j % 4 in
          let control:i32 = imm8 >>! (i *! mk_u64 4 <: u64) in
          if ((control >>! mk_i32 3 <: i32) %! mk_i32 2 <: i32) =. mk_i32 1
          then mk_i32 0
          else
            match control %! mk_i32 4 <: i32 with
            | Rust_primitives.Integers.MkInt 0 -> to_i32x8 a (mk_u64 (0 + offset))
            | Rust_primitives.Integers.MkInt 1 -> to_i32x8 a (mk_u64 (4 + offset))
            | Rust_primitives.Integers.MkInt 2 -> to_i32x8 b (mk_u64 (0 + offset))
            | Rust_primitives.Integers.MkInt 3 -> to_i32x8 b (mk_u64 (4 + offset))
            )
        )
  [SMTPat (to_i32x8 (Libcrux_intrinsics.Avx2.mm256_permute2x128_si256 imm8 a b) j)]

assume val mm256_castsi256_si128_lemma (a: bv256) (i:u64{v i < 4}):
  Lemma (to_i32x4 (Libcrux_intrinsics.Avx2.mm256_castsi256_si128 a) i == to_i32x8 a i)
  [SMTPat (to_i32x4 (Libcrux_intrinsics.Avx2.mm256_castsi256_si128 a) i)]

assume val mm256_unpacklo_epi64_lemma (a b: bv256) (i:u64{v i < 8}):
  Lemma (to_i32x8 (Libcrux_intrinsics.Avx2.mm256_unpacklo_epi64 a b) i ==
       (match i <: u64 with
        | Rust_primitives.Integers.MkInt 0 -> (to_i32x8 a) (mk_u64 0)
        | Rust_primitives.Integers.MkInt 1 -> (to_i32x8 a) (mk_u64 1)
        | Rust_primitives.Integers.MkInt 2 -> (to_i32x8 b) (mk_u64 0)
        | Rust_primitives.Integers.MkInt 3 -> (to_i32x8 b) (mk_u64 1)
        | Rust_primitives.Integers.MkInt 4 -> (to_i32x8 a) (mk_u64 4)
        | Rust_primitives.Integers.MkInt 5 -> (to_i32x8 a) (mk_u64 5)
        | Rust_primitives.Integers.MkInt 6 -> (to_i32x8 b) (mk_u64 4)
        | Rust_primitives.Integers.MkInt 7 -> (to_i32x8 b) (mk_u64 5)
        | _ ->
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

              <:
              Rust_primitives.Hax.t_Never)
          <:
          i32))
  [SMTPat (to_i32x8 (Libcrux_intrinsics.Avx2.mm256_unpacklo_epi64 a b) i)]

assume val mm256_unpackhi_epi64_lemma (a b: bv256) (i:u64{v i < 8}):
  Lemma (to_i32x8 (Libcrux_intrinsics.Avx2.mm256_unpackhi_epi64 a b) i ==
       (match i <: u64 with
        | Rust_primitives.Integers.MkInt 0 -> (to_i32x8 a) ( mk_u64 2 )
        | Rust_primitives.Integers.MkInt 1 -> (to_i32x8 a) ( mk_u64 3 )
        | Rust_primitives.Integers.MkInt 2 -> (to_i32x8 b) ( mk_u64 2 )
        | Rust_primitives.Integers.MkInt 3 -> (to_i32x8 b) ( mk_u64 3 )
        | Rust_primitives.Integers.MkInt 4 -> (to_i32x8 a) ( mk_u64 6 )
        | Rust_primitives.Integers.MkInt 5 -> (to_i32x8 a) ( mk_u64 7 )
        | Rust_primitives.Integers.MkInt 6 -> (to_i32x8 b) ( mk_u64 6 )
        | Rust_primitives.Integers.MkInt 7 -> (to_i32x8 b) ( mk_u64 7 )
        | _ ->
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

              <:
              Rust_primitives.Hax.t_Never)
          <:
          i32))
  [SMTPat (to_i32x8 (Libcrux_intrinsics.Avx2.mm256_unpackhi_epi64 a b) i)]

assume val montgomery_multiply_aux_lemma field_modulus inverse_of_modulus_mod_montgomery_r
  (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  (i:u64{v i < 8}):
  Lemma 
    (requires
        field_modulus ==
        (Libcrux_intrinsics.Avx2.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
          <:
          Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) /\
        inverse_of_modulus_mod_montgomery_r ==
        (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (cast (Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                  <:
                  u64)
              <:
              i32)
          <:
          Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))
  (ensures
    to_i32x8 (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply_aux field_modulus inverse_of_modulus_mod_montgomery_r a b) i ==
    Spec.MLDSA.Ntt.mont_mul (to_i32x8 a i) (to_i32x8 b i))
    [SMTPat (to_i32x8 (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply_aux field_modulus inverse_of_modulus_mod_montgomery_r a b) i)]

let montgomery_multiply_lemma
  (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  (i:u64{v i < 8}):
  Lemma (
    to_i32x8 (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply a b) i ==
    Spec.MLDSA.Ntt.mont_mul (to_i32x8 a i) (to_i32x8 b i))
    [SMTPat (to_i32x8 (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply a b) i)]
   = ()

