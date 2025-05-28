module Libcrux_ml_dsa.Simd.Avx2.Encoding.Gamma1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

open Spec.Intrinsics
let lemma_mm256_add_epi64_lemma_weaker lhs rhs (i: u64 {v i < 256})
  : Lemma
    (requires forall i. Core_models.Abstractions.Bit.Bit_Zero? lhs.(i) \/ Core_models.Abstractions.Bit.Bit_Zero? rhs.(i))
    (ensures (Core_models.Abstractions.Bit.Bit_Zero? lhs.(i) ==> (Libcrux_intrinsics.Avx2.mm256_add_epi64 lhs rhs).(i) == rhs.(i))
           /\ (Core_models.Abstractions.Bit.Bit_Zero? rhs.(i) ==> (Libcrux_intrinsics.Avx2.mm256_add_epi64 lhs rhs).(i) == lhs.(i)))
    [SMTPat (Libcrux_intrinsics.Avx2.mm256_add_epi64 lhs rhs).(i)]
    = Spec.Intrinsics.mm256_add_epi64_lemma lhs rhs i

[@@ "opaque_to_smt"]
#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let serialize_when_gamma1_is_2_pow_17_aux
      (simd_unit_shifted: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (requires
        forall i. v i % 32 >= 18 ==> simd_unit_shifted.(i) == Core_models.Abstractions.Bit.Bit_Zero)
      (ensures
        fun result ->
          let result:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) = result in
          forall (i: nat{i < 8}) (j: nat{j < 18}).
            let offset = if i >= 4 then 56 else 0 in
            result.(mk_int (i * 18 + j + offset)) == simd_unit_shifted.(mk_int (i * 32 + j))) =
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
  let every_second_element:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_bsrli_epi128 (mk_i32 8) adjacent_2_combined
  in
  let every_second_element_shifted:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_slli_epi64 (mk_i32 36) every_second_element
  in
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_add_epi64 adjacent_2_combined every_second_element_shifted
  in
  Libcrux_intrinsics.Avx2.mm256_srlv_epi64 adjacent_4_combined
    (Libcrux_intrinsics.Avx2.mm256_set_epi64x (mk_i64 28) (mk_i64 0) (mk_i64 28) (mk_i64 0)
      <:
      Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))

#pop-options

let v_GAMMA1_2_POW_17_: i32 = mk_i32 1 <<! mk_i32 17

#push-options "--ifuel 0 --z3rlimit 140 --split_queries always"

let serialize_when_gamma1_is_2_pow_17_
      (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        forall i.
          let x = (v v_GAMMA1_2_POW_17_ - v (to_i32x8 simd_unit i)) in
          x >= 0 && x < pow2 18)
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          Seq.length out_future == 18 /\
          (forall (i: nat{i < 144}).
              u8_to_bv (Seq.index out_future (i / 8)) (mk_int (i % 8)) ==
              i32_to_bv (v_GAMMA1_2_POW_17_ `sub_mod` (to_i32x8 simd_unit (mk_int (i / 18))))
                (mk_int (i % 18)))) =
  let serialized:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let simd_unit_shifted:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 (Libcrux_intrinsics.Avx2.mm256_set1_epi32 v_GAMMA1_2_POW_17_

        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      simd_unit
  in
  let _:Prims.unit = i32_lt_pow2_n_to_bit_zero_lemma 18 simd_unit_shifted in
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    serialize_when_gamma1_is_2_pow_17_aux simd_unit_shifted
  in
  let lower_4_:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm256_castsi256_si128 adjacent_4_combined
  in
  let serialized:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = mk_usize 16
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          lower_4_
        <:
        t_Slice u8)
  in
  let upper_4_:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm256_extracti128_si256 (mk_i32 1) adjacent_4_combined
  in
  let serialized:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = mk_usize 9; Core.Ops.Range.f_end = mk_usize 25 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = mk_usize 9;
                Core.Ops.Range.f_end = mk_usize 25
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          upper_4_
        <:
        t_Slice u8)
  in
  let _:Prims.unit =
    let spec (i: nat{i < 144}) =
      u8_to_bv (Seq.index serialized (i / 8)) (mk_int (i % 8)) ==
      i32_to_bv (v_GAMMA1_2_POW_17_ `sub_mod` (to_i32x8 simd_unit (mk_int (i / 18))))
        (mk_int (i % 18))
    in
    let proof:squash (forall i. spec i) =
      assert (forall (i: nat{i < 8}).
            to_i32x8 simd_unit_shifted (mk_int ((i / 4) * 4 + i % 4)) ==
            v_GAMMA1_2_POW_17_
            `sub_mod`
            (to_i32x8 simd_unit (mk_int i)));
      let proof_72 () : squash (forall i. i < 72 ==> spec i) = () in
      let proof_144 () : squash (forall i. i >= 72 ==> spec i) = () in
      proof_72 ();
      proof_144 ()
    in
    ()
  in
  let out:t_Slice u8 =
    Core.Slice.impl__copy_from_slice #u8
      out
      (serialized.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 18 }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  out

#pop-options

[@@ "opaque_to_smt"]
let serialize_when_gamma1_is_2_pow_19_aux
      (simd_unit_shifted: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (requires
        forall i. v i % 32 >= 20 ==> simd_unit_shifted.(i) == Core_models.Abstractions.Bit.Bit_Zero)
      (ensures
        fun result ->
          let result:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) = result in
          forall (i: nat{i < 8}) (j: nat{j < 20}).
            result.(mk_int ((if i >= 4 then 48 else 0) + i * 20 + j)) ==
            simd_unit_shifted.(mk_int (i * 32 + j))) =
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
  Libcrux_intrinsics.Avx2.mm256_shuffle_epi8 adjacent_2_combined
    (Libcrux_intrinsics.Avx2.mm256_set_epi8 (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
        (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 12) (mk_i8 11) (mk_i8 10) (mk_i8 9) (mk_i8 8) (mk_i8 4)
        (mk_i8 3) (mk_i8 2) (mk_i8 1) (mk_i8 0) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
        (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 12) (mk_i8 11) (mk_i8 10) (mk_i8 9) (mk_i8 8) (mk_i8 4)
        (mk_i8 3) (mk_i8 2) (mk_i8 1) (mk_i8 0)
      <:
      Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))

let v_GAMMA1_2_POW_19_: i32 = mk_i32 1 <<! mk_i32 19

#push-options "--ifuel 0 --z3rlimit 140 --split_queries always"

let serialize_when_gamma1_is_2_pow_19_
      (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        forall i.
          let x = (v v_GAMMA1_2_POW_19_ - v (to_i32x8 simd_unit i)) in
          x >= 0 && x < pow2 20)
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          Seq.length out_future == 20 /\
          (forall (i: nat{i < 160}).
              u8_to_bv (Seq.index out_future (i / 8)) (mk_int (i % 8)) ==
              i32_to_bv (v_GAMMA1_2_POW_19_ `sub_mod` (to_i32x8 simd_unit (mk_int (i / 20))))
                (mk_int (i % 20)))) =
  let serialized:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let simd_unit_shifted:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 (Libcrux_intrinsics.Avx2.mm256_set1_epi32 v_GAMMA1_2_POW_19_

        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      simd_unit
  in
  let _:Prims.unit = i32_lt_pow2_n_to_bit_zero_lemma 20 simd_unit_shifted in
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    serialize_when_gamma1_is_2_pow_19_aux simd_unit_shifted
  in
  let lower_4_:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm256_castsi256_si128 adjacent_4_combined
  in
  let serialized:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = mk_usize 16
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          lower_4_
        <:
        t_Slice u8)
  in
  let upper_4_:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm256_extracti128_si256 (mk_i32 1) adjacent_4_combined
  in
  let serialized:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = mk_usize 10; Core.Ops.Range.f_end = mk_usize 26 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = mk_usize 10;
                Core.Ops.Range.f_end = mk_usize 26
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          upper_4_
        <:
        t_Slice u8)
  in
  let _:Prims.unit =
    let spec (i: nat{i < 160}) =
      u8_to_bv (Seq.index serialized (i / 8)) (mk_int (i % 8)) ==
      i32_to_bv (v_GAMMA1_2_POW_19_ `sub_mod` (to_i32x8 simd_unit (mk_int (i / 20))))
        (mk_int (i % 20))
    in
    let proof:squash (forall i. spec i) =
      assert (forall (i: nat{i < 8}).
            to_i32x8 simd_unit_shifted (mk_int ((i / 4) * 4 + i % 4)) ==
            v_GAMMA1_2_POW_19_
            `sub_mod`
            (to_i32x8 simd_unit (mk_int i)));
      let proof_80 () : squash (forall i. i < 80 ==> spec i) = () in
      let proof_160 () : squash (forall i. i >= 80 ==> spec i) = () in
      proof_80 ();
      proof_160 ()
    in
    ()
  in
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

let serialize
      (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (serialized: t_Slice u8)
      (gamma1_exponent: usize)
    : Prims.Pure (t_Slice u8)
      (requires
        (v gamma1_exponent == 17 \/ v gamma1_exponent == 19) /\
        (Seq.length serialized == v gamma1_exponent + 1) /\
        (let gamma_pow =
            match v gamma1_exponent with
            | 17 -> v_GAMMA1_2_POW_17_
            | 19 -> v_GAMMA1_2_POW_19_
          in
          forall i.
            let x = (v gamma_pow - v (to_i32x8 simd_unit i)) in
            x >= 0 && x < pow2 (v gamma1_exponent + 1)))
      (ensures
        fun serialized_future ->
          let serialized_future:t_Slice u8 = serialized_future in
          let gamma_pow =
            match v gamma1_exponent with
            | 17 -> v_GAMMA1_2_POW_17_
            | 19 -> v_GAMMA1_2_POW_19_
          in
          let n_bytes = v gamma1_exponent + 1 in
          Seq.length serialized_future == n_bytes /\
          (forall (i: nat{i < n_bytes * 8}).
              u8_to_bv (Seq.index serialized_future (i / 8)) (mk_int (i % 8)) ==
              i32_to_bv (gamma_pow -! to_i32x8 simd_unit (mk_int (i / n_bytes)))
                (mk_int (i % n_bytes)))) =
  let serialized:t_Slice u8 =
    match cast (gamma1_exponent <: usize) <: u8 with
    | Rust_primitives.Integers.MkInt 17 -> serialize_when_gamma1_is_2_pow_17_ simd_unit serialized
    | Rust_primitives.Integers.MkInt 19 -> serialize_when_gamma1_is_2_pow_19_ simd_unit serialized
    | _ -> serialized
  in
  serialized

let deserialize_when_gamma1_is_2_pow_17___v_GAMMA1: i32 = mk_i32 1 <<! mk_i32 17

let deserialize_when_gamma1_is_2_pow_17___v_GAMMA1_TIMES_2_MASK: i32 =
  (deserialize_when_gamma1_is_2_pow_17___v_GAMMA1 <<! mk_i32 1 <: i32) -! mk_i32 1

let assert_lemma (phi: Type0 {phi}): unit -> Lemma phi = fun _ -> ()

let lemma_and vec i
  : Lemma (
       (Libcrux_intrinsics.Avx2.mm256_and_si256 vec (Libcrux_intrinsics.Avx2.mm256_set1_epi32 deserialize_when_gamma1_is_2_pow_17___v_GAMMA1_TIMES_2_MASK)).(i)
    == (if v i % 32 >= 18 then Core_models.Abstractions.Bit.Bit_Zero else vec.(i))
  ) [SMTPat ((Libcrux_intrinsics.Avx2.mm256_and_si256 vec (Libcrux_intrinsics.Avx2.mm256_set1_epi32 deserialize_when_gamma1_is_2_pow_17___v_GAMMA1_TIMES_2_MASK)).(i))]= 
    assert (deserialize_when_gamma1_is_2_pow_17___v_GAMMA1_TIMES_2_MASK == (mk_i32 1 <<! mk_i32 18) -! mk_int 1);
    admit ()


assume val eq_to_i32x8 a b (i: _{v i < 8})
  : Lemma 
    (requires forall (j: nat{j < 32}). a.(mk_int (v i * 32 + j)) == b.(mk_int (v i * 32 + j)))
    (ensures to_i32x8 a i == to_i32x8 b i)
    [SMTPat (to_i32x8 a i == to_i32x8 b i)]

#push-options "--ifuel 0 --split_queries always --z3rlimit 80"
let deserialize_when_gamma1_is_2_pow_17_
      (serialized: t_Slice u8 {Seq.length serialized == 18})
      (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Pure (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
           (requires True)
           // (ensures fun _ -> True)
           (ensures fun out -> forall (i: nat {i < 72}). out.(mk_int ((i / 18) * 32 + i % 18)) == u8_to_bv (Seq.index serialized (i / 8)) (mk_int (i % 8)))
      =
      let serialized0 = serialized in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. mk_usize 18 <: bool)
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
  // let left (): squash (forall (i: nat {i < 72}).
  //      coefficients.(mk_int ((i / 18) * 32 + i % 18)) 
  //   == serialized_lower.(mk_int i)
  // ) = () in
  // let right (): squash (forall (i: nat {i < 72}).
  //      coefficients.(mk_int (128 + (i / 18) * 32 + i % 18)) 
  //   == serialized_upper.(mk_int (56 + (i % 72)))
  // ) = () in
  // left (); right ();
  // assert(forall (i: nat {i < 144}). coefficients.(mk_int ((i / 18) * 32 + i % 18)) == u8_to_bv (Seq.index serialized0 (i / 8)) (mk_int (i % 8)));
  let cc = coefficients in
  let coefficients:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_and_si256 coefficients
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 deserialize_when_gamma1_is_2_pow_17___v_GAMMA1_TIMES_2_MASK

        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  // lemma_and cc (mk_int 0);
  // assert (forall (i: nat {i < 144}). cc.(mk_int ((i / 18) * 32 + i % 18)) == coefficients.(mk_int ((i / 18) * 32 + i % 18)));
  // assert (forall (i: nat {i < 144}). coefficients.(mk_int ((i / 18) * 32 + i % 18)) == u8_to_bv (Seq.index serialized0 (i / 8)) (mk_int (i % 8)));
  let out:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 (Libcrux_intrinsics.Avx2.mm256_set1_epi32 deserialize_when_gamma1_is_2_pow_17___v_GAMMA1

        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      coefficients
  in
  assert (forall (i: nat {i < 256}). i % 32 >= 18 ==> coefficients.(mk_int i) == Core_models.Abstractions.Bit.Bit_Zero);
  let serialized_i32s = Core_models.Abstractions.Bitvec.impl_9__from_fn (mk_int 256)  (fun (i:u64{v i < 256}) ->
    let i32_block = v i / 32 in
    let i18_index = i32_block * 18 + v i % 32 in
    if v i % 32 >= 18 
    then Core_models.Abstractions.Bit.Bit_Zero 
    else u8_to_bv (Seq.index serialized0 (i18_index / 8)) (mk_int (i18_index % 8))
  ) in
  assert (forall i. to_i32x8 coefficients i == to_i32x8 serialized_i32s i);
  // assert (forall (i: nat {i < 144}). coefficients.(mk_int ((i / 18) * 32 + i % 18)) == u8_to_bv (Seq.index serialized0 (i / 8)) (mk_int (i % 8)));
  // assert (forall (i: nat {i < 144}).
  //           to_i32x8 out (mk_int (i / 18))
  //        == deserialize_when_gamma1_is_2_pow_17___v_GAMMA1 `sub_mod` (to_i32x8 coefficients (mk_int (i / 18)))
  //        );
  // assert (forall (i: nat {i < 144}). 
  //           i32_to_bv (to_i32x8 out (mk_int (i / 18))) (mk_int (i % 18)) 
  //        == coefficients.(mk_int ((i / 18) * 32 + i % 18))
  //        );
  admit ();
  out


let deserialize_when_gamma1_is_2_pow_19___v_GAMMA1: i32 = mk_i32 1 <<! mk_i32 19

let deserialize_when_gamma1_is_2_pow_19___v_GAMMA1_TIMES_2_MASK: i32 =
  (deserialize_when_gamma1_is_2_pow_19___v_GAMMA1 <<! mk_i32 1 <: i32) -! mk_i32 1

let deserialize_when_gamma1_is_2_pow_19_
      (serialized: t_Slice u8)
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
