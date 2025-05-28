module Libcrux_ml_dsa.Simd.Avx2.Encoding.T0
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let v_MAGIC_NUMBER: i32 =
  mk_i32 1 <<! (Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T -! mk_usize 1 <: usize)

let change_interval (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let interval_end:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_set1_epi32 v_MAGIC_NUMBER
  in
  Libcrux_intrinsics.Avx2.mm256_sub_epi32 interval_end simd_unit

open Spec.Intrinsics

let mm256_add_epi64_lemma_smtpat lhs rhs (i: u64 {v i < 256})
  : Lemma
    (requires 
      forall (j:nat{j < v i % 64}). Core_models.Abstractions.Bit.Bit_Zero? lhs.(mk_int ((v i / 64) * 64 + j))
                         \/ Core_models.Abstractions.Bit.Bit_Zero? rhs.(mk_int ((v i / 64) * 64 + j))
    )
    (ensures  
      (Core_models.Abstractions.Bit.Bit_Zero? lhs.(i) ==> (Libcrux_intrinsics.Avx2.mm256_add_epi64 lhs rhs).(i) == rhs.(i)) /\
      (Core_models.Abstractions.Bit.Bit_Zero? rhs.(i) ==> (Libcrux_intrinsics.Avx2.mm256_add_epi64 lhs rhs).(i) == lhs.(i))
    )
    [SMTPat (Libcrux_intrinsics.Avx2.mm256_add_epi64 lhs rhs).(i)]
    = mm256_add_epi64_lemma lhs rhs i

#push-options "--fuel 0 --ifuel 0 --z3rlimit 500"

let serialize_aux (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
      (requires forall i. v i % 32 >= 13 ==> simd_unit.(i) == Core_models.Abstractions.Bit.Bit_Zero)
      (ensures
        fun out ->
          let out:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) = out in
          forall (i: nat{i < 8}) (j: nat{j < 13}).
            out.(mk_int (i * 13 + j)) == simd_unit.(mk_int (i * 32 + j))) =
  let adjacent_2_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sllv_epi32 simd_unit
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 19)
          (mk_i32 0)
          (mk_i32 19)
          (mk_i32 0)
          (mk_i32 19)
          (mk_i32 0)
          (mk_i32 19)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_2_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srli_epi64 (mk_i32 19) adjacent_2_combined
  in
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_permutevar8x32_epi32 adjacent_2_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 6)
          (mk_i32 4)
          (mk_i32 2)
          (mk_i32 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sllv_epi32 adjacent_4_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 6)
          (mk_i32 0)
          (mk_i32 6)
          (mk_i32 0)
          (mk_i32 6)
          (mk_i32 0)
          (mk_i32 6)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srli_epi64 (mk_i32 6) adjacent_4_combined
  in
  let second_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_bsrli_epi128 (mk_i32 8) adjacent_4_combined
  in
  let least_12_bits_shifted_up:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_slli_epi64 (mk_i32 52) second_4_combined
  in
  let bits_sequential:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_add_epi64 adjacent_4_combined least_12_bits_shifted_up
  in
  let bits_sequential:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srlv_epi64 bits_sequential
      (Libcrux_intrinsics.Avx2.mm256_set_epi64x (mk_i64 0) (mk_i64 0) (mk_i64 12) (mk_i64 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  Libcrux_intrinsics.Avx2.mm256_castsi256_si128 bits_sequential

#pop-options

#push-options "--ifuel 0 --z3rlimit 140 --split_queries always"

let serialize (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        forall i.
          let x = (v v_MAGIC_NUMBER - v (to_i32x8 simd_unit i)) in
          x >= 0 && x < pow2 13)
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          Seq.length out_future == 13 /\
          (forall (i: nat{i < 8 * 13}).
              u8_to_bv (Seq.index out_future (i / 8)) (mk_int (i % 8)) ==
              i32_to_bv (v_MAGIC_NUMBER `sub_mod` (to_i32x8 simd_unit (mk_int (i / 13))))
                (mk_int (i % 13)))) =
  let serialized:t_Array u8 (mk_usize 16) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 16) in
  let simd_unit_changed:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    change_interval simd_unit
  in
  let _:Prims.unit = i32_lt_pow2_n_to_bit_zero_lemma 13 simd_unit_changed in
  let bits_sequential:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    serialize_aux simd_unit_changed
  in
  let serialized:t_Array u8 (mk_usize 16) =
    Libcrux_intrinsics.Avx2.mm_storeu_bytes_si128 serialized bits_sequential
  in
  let _:Prims.unit =
    assert (forall (i: nat{i < 104}).
          to_i32x8 simd_unit_changed (mk_int (i / 13)) ==
          v_MAGIC_NUMBER
          `sub_mod`
          (to_i32x8 simd_unit (mk_int (i / 13))));
    assert (forall i.
          v_MAGIC_NUMBER `sub_mod` (to_i32x8 simd_unit i) == v_MAGIC_NUMBER -! to_i32x8 simd_unit i)
  in
  let out:t_Slice u8 =
    Core.Slice.impl__copy_from_slice #u8
      out
      (serialized.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 13 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  out

#pop-options

let deserialize__v_COEFFICIENT_MASK: i32 = (mk_i32 1 <<! mk_i32 13 <: i32) -! mk_i32 1

let deserialize
      (serialized: t_Slice u8 {Seq.length serialized == 13})
      (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.impl__len #u8 serialized, mk_usize 13 <: (usize & usize) with
        | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
      in
      ()
  in
  let serialized_extended:t_Array u8 (mk_usize 16) =
    Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 16)
  in
  let serialized_extended:t_Array u8 (mk_usize 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized_extended
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 13 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (serialized_extended.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = mk_usize 13
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          serialized
        <:
        t_Slice u8)
  in
  let serialized:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm_loadu_si128 (serialized_extended <: t_Slice u8)
  in
  let serialized:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_set_m128i serialized serialized
  in
  let coefficients:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_shuffle_epi8 serialized
      (Libcrux_intrinsics.Avx2.mm256_set_epi8 (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 12) (mk_i8 11)
          (mk_i8 (-1)) (mk_i8 11) (mk_i8 10) (mk_i8 9) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 9) (mk_i8 8)
          (mk_i8 (-1)) (mk_i8 8) (mk_i8 7) (mk_i8 6) (mk_i8 (-1)) (mk_i8 6) (mk_i8 5) (mk_i8 4)
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 4) (mk_i8 3) (mk_i8 (-1)) (mk_i8 3) (mk_i8 2) (mk_i8 1)
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 1) (mk_i8 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let coefficients:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srlv_epi32 coefficients
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 3)
          (mk_i32 6)
          (mk_i32 1)
          (mk_i32 4)
          (mk_i32 7)
          (mk_i32 2)
          (mk_i32 5)
          (mk_i32 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let coefficients:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_and_si256 coefficients
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 deserialize__v_COEFFICIENT_MASK
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let out:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) = change_interval coefficients in
  out
