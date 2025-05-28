module Libcrux_ml_dsa.Simd.Avx2.Encoding.Gamma1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

open Spec.Intrinsics
module U = Spec.Utils

let serialize_when_gamma1_is_2_pow_17___v_GAMMA1: i32 = mk_i32 1 <<! mk_i32 17

let lemma_mm256_add_epi64_lemma_weaker lhs rhs (i: u64 {v i < 256})
  : Lemma 
    (requires forall i. Core_models.Abstractions.Bit.Bit_Zero? lhs.(i) \/ Core_models.Abstractions.Bit.Bit_Zero? rhs.(i))
    (ensures (Core_models.Abstractions.Bit.Bit_Zero? lhs.(i) ==> (Libcrux_intrinsics.Avx2.mm256_add_epi64 lhs rhs).(i) == rhs.(i))
           /\ (Core_models.Abstractions.Bit.Bit_Zero? rhs.(i) ==> (Libcrux_intrinsics.Avx2.mm256_add_epi64 lhs rhs).(i) == lhs.(i)))
    [SMTPat (Libcrux_intrinsics.Avx2.mm256_add_epi64 lhs rhs).(i)]
    = Spec.Intrinsics.lemma_mm256_add_epi64_lemma lhs rhs i

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
let serialize_when_gamma1_is_2_pow_17_
      (simd_unit_shifted: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (out: t_Slice u8)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
    =
  // let serialized:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  // let simd_unit_shifted:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  //   Libcrux_intrinsics.Avx2.mm256_sub_epi32 (Libcrux_intrinsics.Avx2.mm256_set1_epi32 serialize_when_gamma1_is_2_pow_17___v_GAMMA1

  //       <:
  //       Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  //     simd_unit
  // in
  assume (forall i. v i % 32 >= 18 ==> simd_unit_shifted.(i) == Core_models.Abstractions.Bit.Bit_Zero);
  let adjacent_2_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sllv_epi32 simd_unit_shifted
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 14)
          (mk_i32 0)
          (mk_i32 14)
          (mk_i32 0)
          (mk_i32 14)
          (mk_i32 0)
          (mk_i32 14)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_2_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srli_epi64 (mk_i32 14) adjacent_2_combined
  in
  // assert (let i = mk_int  in simd_unit_shifted.(i) == adjacent_2_combined.(mk_int 18));
  // admit ()
  let every_second_element:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_bsrli_epi128 (mk_i32 8) adjacent_2_combined
  in
  let every_second_element_shifted:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_slli_epi64 (mk_i32 36) every_second_element
  in
  // assert_spinoff (forall (j: nat {j < 18}). adjacent_2_combined.(mk_int j) == simd_unit_shifted.(mk_int j));
  // assert_spinoff (forall (j: nat {j < 18}). adjacent_2_combined.(mk_int (18 + j)) == simd_unit_shifted.(mk_int (32 + j)));
  // admit ()
  // assert (forall i. 
  //   Core_models.Abstractions.Bit.Bit_Zero? adjacent_2_combined.(i) \/
  //   Core_models.Abstractions.Bit.Bit_Zero? every_second_element_shifted.(i)
  // );
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_add_epi64 adjacent_2_combined every_second_element_shifted
  in
  
  // assert (forall i.
  //   let lhs = adjacent_2_combined in let rhs = every_second_element_shifted in
  //   (Core_models.Abstractions.Bit.Bit_Zero? lhs.(i) 
  //     ==> (Libcrux_intrinsics.Avx2.mm256_add_epi64 lhs rhs).(i) == rhs.(i)) /\
  //     (Core_models.Abstractions.Bit.Bit_Zero? rhs.(i)
  //     ==> (Libcrux_intrinsics.Avx2.mm256_add_epi64 lhs rhs).(i) == lhs.(i))
  // );
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srlv_epi64 adjacent_4_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi64x (mk_i64 28) (mk_i64 0) (mk_i64 28) (mk_i64 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  
  assert (
    forall (i: nat {i < 8}).
    // let i = 1 in
    // let j = 0 in
    forall (j: nat {j < 18}).
    let offset = if i >= 4 then 56 else 0 in
    adjacent_4_combined.(mk_int (i * 18 + j + offset)) == simd_unit_shifted.(mk_int (i * 32 + j))
  );
  // assert (//forall (i: nat {i < 50}). 
  //   let i = 0 in
  //   adjacent_4_combined.(mk_int i) == simd_unit_shifted.(mk_int ((i / 18) * 32 + i % 18))
  // );
  adjacent_4_combined
#pop-options

let serialize_when_gamma1_is_2_pow_19___v_GAMMA1: i32 = mk_i32 1 <<! mk_i32 19

// #push-options "--fuel 0 --ifuel 0 --z3rlimit 600 --split_queries always --z3smtopt '(set-option :smt.arith.nl false)'"
let serialize_when_gamma1_is_2_pow_19_
      (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (out: t_Slice u8)
    : t_Slice u8 =
  let serialized:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let simd_unit_shifted:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 (Libcrux_intrinsics.Avx2.mm256_set1_epi32 serialize_when_gamma1_is_2_pow_19___v_GAMMA1

        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      simd_unit
  in
  assume (forall i. v i % 32 >= 20 ==> simd_unit_shifted.(i) == Core_models.Abstractions.Bit.Bit_Zero);
  let adjacent_2_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sllv_epi32 simd_unit_shifted
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 12)
          (mk_i32 0)
          (mk_i32 12)
          (mk_i32 0)
          (mk_i32 12)
          (mk_i32 0)
          (mk_i32 12)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_2_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srli_epi64 (mk_i32 12) adjacent_2_combined
  in
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_shuffle_epi8 adjacent_2_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi8 (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 12) (mk_i8 11) (mk_i8 10) (mk_i8 9) (mk_i8 8) (mk_i8 4)
          (mk_i8 3) (mk_i8 2) (mk_i8 1) (mk_i8 0) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 12) (mk_i8 11) (mk_i8 10) (mk_i8 9)
          (mk_i8 8) (mk_i8 4) (mk_i8 3) (mk_i8 2) (mk_i8 1) (mk_i8 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  assert (forall (i: nat {i < 8}) (j: nat {j < 20}).
    (adjacent_4_combined.(mk_int ((if i >= 4 then 67  else 0) + i * 20 + j)))
    == simd_unit_shifted.(mk_int (i * 32 + j))
  );  
  admit ()
  let lower_4_:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm256_castsi256_si128 adjacent_4_combined
  in
  let serialized_lower = (Libcrux_intrinsics.Avx2.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = mk_usize 16
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          lower_4_
        <:
        t_Slice u8) in
  let serialized:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 16 }
        <:
        Core.Ops.Range.t_Range usize)
      serialized_lower
  in
  let upper_4_:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm256_extracti128_si256 (mk_i32 1) adjacent_4_combined
  in
  assert (forall (i: nat {i < 8}) (j: nat {j < 20}).
    (if i < 4 then lower_4_.(mk_int (i * 20 + j))
              else upper_4_.(mk_int ((i - 4) * 20 + j)))
    == simd_unit_shifted.(mk_int (i * 32 + j))
  );  
  let serialized_upper = (Libcrux_intrinsics.Avx2.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = mk_usize 10;
                Core.Ops.Range.f_end = mk_usize 26
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          upper_4_
        <:
        t_Slice u8) in
  let serialized:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = mk_usize 10; Core.Ops.Range.f_end = mk_usize 26 }
        <:
        Core.Ops.Range.t_Range usize)
      serialized_upper
  in
  // assert (forall (i:nat {i < 20}).
  //   Seq.index serialized i
  //   == (
  //     if i < 10 then Seq.index serialized_lower i else Seq.index serialized_upper (i - 10)
  //   )
  // );
  assert (
    forall (i: nat {i < 160}).
    u8_to_bv (Seq.index serialized (i / 8)) (mk_int (i % 8)) == 
    simd_unit_shifted.(mk_int ((i / 20) * 32 + (i % 20)))
  );
  let out:t_Slice u8 =
    Core.Slice.impl__copy_from_slice #u8
      out
      (serialized.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 20 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  out
#pop-options

// let serialize
//       (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
//       (serialized: t_Slice u8)
//       (gamma1_exponent: usize)
//     : t_Slice u8 =
//   let serialized:t_Slice u8 =
//     match cast (gamma1_exponent <: usize) <: u8 with
//     | Rust_primitives.Integers.MkInt 17 -> serialize_when_gamma1_is_2_pow_17_ simd_unit serialized
//     | Rust_primitives.Integers.MkInt 19 -> serialize_when_gamma1_is_2_pow_19_ simd_unit serialized
//     | _ -> serialized
//   in
//   serialized

let deserialize_when_gamma1_is_2_pow_17___v_GAMMA1: i32 = mk_i32 1 <<! mk_i32 17

let deserialize_when_gamma1_is_2_pow_17___v_GAMMA1_TIMES_2_MASK: i32 =
  (deserialize_when_gamma1_is_2_pow_17___v_GAMMA1 <<! mk_i32 1 <: i32) -! mk_i32 1

#push-options "--ifuel 0 --split_queries always"
let deserialize_when_gamma1_is_2_pow_17_
      (serialized: t_Slice u8 {Seq.length serialized == 18})
      (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let serialized_lower:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm_loadu_si128 (serialized.[ {
            Core.Ops.Range.f_start = mk_usize 0;
            Core.Ops.Range.f_end = mk_usize 16
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let serialized_upper:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm_loadu_si128 (serialized.[ {
            Core.Ops.Range.f_start = mk_usize 2;
            Core.Ops.Range.f_end = mk_usize 18
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let serialized:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_set_m128i serialized_upper serialized_lower
  in
  let coefficients:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_shuffle_epi8 serialized
      (Libcrux_intrinsics.Avx2.mm256_set_epi8 (mk_i8 (-1)) (mk_i8 15) (mk_i8 14) (mk_i8 13)
          (mk_i8 (-1)) (mk_i8 13) (mk_i8 12) (mk_i8 11) (mk_i8 (-1)) (mk_i8 11) (mk_i8 10) (mk_i8 9)
          (mk_i8 (-1)) (mk_i8 9) (mk_i8 8) (mk_i8 7) (mk_i8 (-1)) (mk_i8 8) (mk_i8 7) (mk_i8 6)
          (mk_i8 (-1)) (mk_i8 6) (mk_i8 5) (mk_i8 4) (mk_i8 (-1)) (mk_i8 4) (mk_i8 3) (mk_i8 2)
          (mk_i8 (-1)) (mk_i8 2) (mk_i8 1) (mk_i8 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let coefficients0 = coefficients in
  let coefficients:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srlv_epi32 coefficients
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 6)
          (mk_i32 4)
          (mk_i32 2)
          (mk_i32 0)
          (mk_i32 6)
          (mk_i32 4)
          (mk_i32 2)
          (mk_i32 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  assert (forall (i: nat {i < 72}).
       coefficients.(mk_int ((i / 18) * 32 + i % 18)) 
    == serialized_lower.(mk_int i)
  );
  assert (forall (i: nat {i < 72}).
       coefficients.(mk_int (128 + (i / 18) * 32 + i % 18)) 
    == serialized_upper.(mk_int (56 + (i % 72)))
  );
  admit ();
  let coefficients:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_and_si256 coefficients
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 deserialize_when_gamma1_is_2_pow_17___v_GAMMA1_TIMES_2_MASK

        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let out:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 (Libcrux_intrinsics.Avx2.mm256_set1_epi32 deserialize_when_gamma1_is_2_pow_17___v_GAMMA1

        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      coefficients
  in
  out
#pop-options

let deserialize_when_gamma1_is_2_pow_19___v_GAMMA1: i32 = mk_i32 1 <<! mk_i32 19

let deserialize_when_gamma1_is_2_pow_19___v_GAMMA1_TIMES_2_MASK: i32 =
  (deserialize_when_gamma1_is_2_pow_19___v_GAMMA1 <<! mk_i32 1 <: i32) -! mk_i32 1

let deserialize_when_gamma1_is_2_pow_19_
      (serialized: t_Slice u8 {Seq.length serialized == 20})
      (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. mk_usize 20 <: bool)
      in
      ()
  in
  let serialized_lower:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm_loadu_si128 (serialized.[ {
            Core.Ops.Range.f_start = mk_usize 0;
            Core.Ops.Range.f_end = mk_usize 16
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let serialized_upper:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm_loadu_si128 (serialized.[ {
            Core.Ops.Range.f_start = mk_usize 4;
            Core.Ops.Range.f_end = mk_usize 20
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let serialized:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_set_m128i serialized_upper serialized_lower
  in
  let coefficients:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_shuffle_epi8 serialized
      (Libcrux_intrinsics.Avx2.mm256_set_epi8 (mk_i8 (-1)) (mk_i8 15) (mk_i8 14) (mk_i8 13)
          (mk_i8 (-1)) (mk_i8 13) (mk_i8 12) (mk_i8 11) (mk_i8 (-1)) (mk_i8 10) (mk_i8 9) (mk_i8 8)
          (mk_i8 (-1)) (mk_i8 8) (mk_i8 7) (mk_i8 6) (mk_i8 (-1)) (mk_i8 9) (mk_i8 8) (mk_i8 7)
          (mk_i8 (-1)) (mk_i8 7) (mk_i8 6) (mk_i8 5) (mk_i8 (-1)) (mk_i8 4) (mk_i8 3) (mk_i8 2)
          (mk_i8 (-1)) (mk_i8 2) (mk_i8 1) (mk_i8 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let coefficients:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srlv_epi32 coefficients
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 4)
          (mk_i32 0)
          (mk_i32 4)
          (mk_i32 0)
          (mk_i32 4)
          (mk_i32 0)
          (mk_i32 4)
          (mk_i32 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  assert (
    forall (i:nat{i < 80}).
      coefficients.(mk_int ((i / 20) * 32 + i % 20)) == serialized_lower.(mk_int (i))
  );
  // TODO: figure out offset
  // assert (
  //   forall (i:nat{i < 80}).
  //     coefficients.(mk_int (128 + (i / 20) * 32 + i % 20)) == serialized_upper.(mk_int (40 + i))
  // );
  let coefficients:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_and_si256 coefficients
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 deserialize_when_gamma1_is_2_pow_19___v_GAMMA1_TIMES_2_MASK

        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let out:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 (Libcrux_intrinsics.Avx2.mm256_set1_epi32 deserialize_when_gamma1_is_2_pow_19___v_GAMMA1

        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      coefficients
  in
  out

let deserialize
      (serialized: t_Slice u8)
      (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (gamma1_exponent: usize)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let out:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    match cast (gamma1_exponent <: usize) <: u8 with
    | Rust_primitives.Integers.MkInt 17 -> deserialize_when_gamma1_is_2_pow_17_ serialized out
    | Rust_primitives.Integers.MkInt 19 -> deserialize_when_gamma1_is_2_pow_19_ serialized out
    | _ -> out
  in
  out
