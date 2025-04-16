module Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Minicore.Abstractions.Funarr in
  ()

irreducible

let v_MANUAL_NORM: Prims.unit = () <: Prims.unit

let manual_norm_lemma (_: Prims.unit) : Lemma (ensures v_MANUAL_NORM == (() <: Prims.unit)) = ()

let mm256_set1_epi32 (x: i32) : Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Minicore.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun e_i ->
        let e_i:u64 = e_i in
        x)

[@@strict_on_arguments [0]]

let shift_32_ (_: Prims.unit) (x: i64) : i64 = x >>! mk_i32 32

[@@strict_on_arguments [0]]

let cast_i64_as_i32 (_: Prims.unit) (x: i64) : i32 = cast (x <: i64) <: i32

[@@strict_on_arguments [0]]

let mul (_: Prims.unit) (x: i32) (y: i32) : i64 =
  (cast (x <: i32) <: i64) *! (cast (y <: i32) <: i64)

[@@strict_on_arguments [0]]

let sub (_: Prims.unit) (x: i32) (y: i32) : i32 =
  cast ((cast (x <: i32) <: i64) -! (cast (y <: i32) <: i64) <: i64) <: i32

let vec_4_i16_to_vec_8_i32 (x: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    : Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Minicore.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        let value:i64 = x.[ i /! mk_u64 2 <: u64 ] in
        cast_i64_as_i32 v_MANUAL_NORM
          (if (i %! mk_u64 2 <: u64) =. mk_u64 0 <: bool
            then value
            else shift_32_ v_MANUAL_NORM value <: i64))

let mm256_mul_epi32 (x y: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
  Minicore.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i64
    (fun i ->
        let i:u64 = i in
        mul v_MANUAL_NORM (x.[ i *! mk_u64 2 <: u64 ] <: i32) (y.[ i *! mk_u64 2 <: u64 ] <: i32)
        <:
        i64)

let mm256_sub_epi32 (x y: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Minicore.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        sub v_MANUAL_NORM (x.[ i ] <: i32) (y.[ i ] <: i32) <: i32)

let mm256_shuffle_epi32 (x: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  let (indexes: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) u64):Minicore.Abstractions.Funarr.t_FunArray
    (mk_u64 4) u64 =
    Minicore.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
      #u64
      (fun i ->
          let i:u64 = i in
          match i <: u64 with
          | Rust_primitives.Integers.MkInt 0 | Rust_primitives.Integers.MkInt 1 -> mk_u64 1
          | _ -> mk_u64 3)
  in
  Minicore.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        if i <. mk_u64 4 <: bool
        then x.[ indexes.[ i ] <: u64 ] <: i32
        else x.[ mk_u64 4 +! (indexes.[ i -! mk_u64 4 <: u64 ] <: u64) <: u64 ] <: i32)

let mm256_blend_epi32 (x y: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Minicore.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        if (i %! mk_u64 2 <: u64) =. mk_u64 0 <: bool then x.[ i ] <: i32 else y.[ i ] <: i32)

assume
val bv_of_vec_8_i32': e_vec: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32
  -> Minicore.Core_arch.X86.t_e_ee_m256i

unfold let bv_of_vec_8_i32 = bv_of_vec_8_i32'

assume
val bv_of_vec_4_i64': e_vec: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64
  -> Minicore.Core_arch.X86.t_e_ee_m256i

unfold let bv_of_vec_4_i64 = bv_of_vec_4_i64'

assume
val vec_4_i64_of_bv': e_bv: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64

unfold let vec_4_i64_of_bv = vec_4_i64_of_bv'

assume
val vec_8_i32_of_bv': e_bv: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32

unfold let vec_8_i32_of_bv = vec_8_i32_of_bv'

assume
val identity_vec_8_i32_inv': x: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32
  -> Lemma
    (ensures
      (vec_8_i32_of_bv (bv_of_vec_8_i32 x <: Minicore.Core_arch.X86.t_e_ee_m256i)
        <:
        Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32) ==
      x)
      [SMTPat (vec_8_i32_of_bv (bv_of_vec_8_i32 x))]

unfold let identity_vec_8_i32_inv = identity_vec_8_i32_inv'

assume
val identity_vec_4_i64_inv': x: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64
  -> Lemma
    (ensures
      (vec_4_i64_of_bv (bv_of_vec_4_i64 x <: Minicore.Core_arch.X86.t_e_ee_m256i)
        <:
        Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64) ==
      x)
      [SMTPat (vec_4_i64_of_bv (bv_of_vec_4_i64 x))]

unfold let identity_vec_4_i64_inv = identity_vec_4_i64_inv'

assume
val identity_vec_8_i32': x: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Lemma
    (ensures
      (bv_of_vec_8_i32 (vec_8_i32_of_bv x <: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i) ==
      x)
      [SMTPat (bv_of_vec_8_i32 (vec_8_i32_of_bv x))]

unfold let identity_vec_8_i32 = identity_vec_8_i32'

assume
val identity_vec_4_i64': x: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Lemma
    (ensures
      (bv_of_vec_4_i64 (vec_4_i64_of_bv x <: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i) ==
      x)
      [SMTPat (bv_of_vec_4_i64 (vec_4_i64_of_bv x))]

unfold let identity_vec_4_i64 = identity_vec_4_i64'

assume
val eq_mm256_blend_epi32': x: Minicore.Core_arch.X86.t_e_ee_m256i -> y: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Lemma
    (ensures
      (Libcrux_intrinsics.Avx2.mm256_blend_epi32 (mk_i32 170) x y <: Minicore.Core_arch.X86.t_e_ee_m256i
      ) ==
      (bv_of_vec_8_i32 (mm256_blend_epi32 (vec_8_i32_of_bv x
                <:
                Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              (vec_8_i32_of_bv y <: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i))

let eq_mm256_blend_epi32 = eq_mm256_blend_epi32'

assume
val eq_mm256_set1_epi32': x: i32
  -> Lemma
    (ensures
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 x <: Minicore.Core_arch.X86.t_e_ee_m256i) ==
      (bv_of_vec_8_i32 (mm256_set1_epi32 x <: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32
          )
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i))

let eq_mm256_set1_epi32 = eq_mm256_set1_epi32'

assume
val eq_mm256_mul_epi32': x: Minicore.Core_arch.X86.t_e_ee_m256i -> y: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Lemma
    (ensures
      (Libcrux_intrinsics.Avx2.mm256_mul_epi32 x y <: Minicore.Core_arch.X86.t_e_ee_m256i) ==
      (bv_of_vec_8_i32 (vec_4_i16_to_vec_8_i32 (mm256_mul_epi32 (vec_8_i32_of_bv x
                    <:
                    Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
                  (vec_8_i32_of_bv y <: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
                <:
                Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
            <:
            Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i))

let eq_mm256_mul_epi32 = eq_mm256_mul_epi32'

assume
val eq_mm256_sub_epi32': x: Minicore.Core_arch.X86.t_e_ee_m256i -> y: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Lemma
    (ensures
      (Libcrux_intrinsics.Avx2.mm256_sub_epi32 x y <: Minicore.Core_arch.X86.t_e_ee_m256i) ==
      (bv_of_vec_8_i32 (mm256_sub_epi32 (vec_8_i32_of_bv x
                <:
                Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              (vec_8_i32_of_bv y <: Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i))

let eq_mm256_sub_epi32 = eq_mm256_sub_epi32'

assume
val eq_mm256_shuffle_epi32': x: Minicore.Core_arch.X86.t_e_ee_m256i
  -> Lemma
    (ensures
      (Libcrux_intrinsics.Avx2.mm256_shuffle_epi32 (mk_i32 245) x <: Minicore.Core_arch.X86.t_e_ee_m256i
      ) ==
      (bv_of_vec_8_i32 (mm256_shuffle_epi32 (vec_8_i32_of_bv x
                <:
                Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i))

let eq_mm256_shuffle_epi32 = eq_mm256_shuffle_epi32'
