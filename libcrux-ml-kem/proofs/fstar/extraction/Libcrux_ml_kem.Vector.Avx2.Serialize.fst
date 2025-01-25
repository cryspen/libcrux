module Libcrux_ml_kem.Vector.Avx2.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Portable in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

#push-options "--ext context_pruning --compat_pre_core 0"

let serialize_1_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let lsb_to_msb:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi16 (mk_i32 15) vector
  in
  let low_msbs:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 lsb_to_msb
  in
  let high_msbs:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 (mk_i32 1) lsb_to_msb
  in
  let msbs:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_packs_epi16 low_msbs high_msbs
  in
  let _:Prims.unit =
    let bits_packed' = BitVec.Intrinsics.mm_movemask_epi8_bv msbs in
    FStar.Tactics.Effect.assert_by_tactic (forall (i: nat{i < 16}).
          bits_packed' i = vector ((i / 1) * 16 + i % 1))
      (fun _ ->
          ();
          (Tactics.Utils.prove_forall_nat_pointwise (fun _ ->
                  Tactics.compute ();
                  Tactics.smt_sync ())))
  in
  let bits_packed:i32 = Libcrux_intrinsics.Avx2_extract.mm_movemask_epi8 msbs in
  let result:t_Array u8 (mk_usize 2) =
    let list = [cast (bits_packed <: i32) <: u8; cast (bits_packed >>! mk_i32 8 <: i32) <: u8] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
    Rust_primitives.Hax.array_of_list 2 list
  in
  let _:Prims.unit =
    assert (forall (i: nat{i < 8}).
          get_bit (bits_packed >>! (mk_i32 8) <: i32) (sz i) == get_bit bits_packed (sz (i + 8)))
  in
  result

#pop-options

#push-options "--ext context_pruning"

[@@"opaque_to_smt"]

let deserialize_1___deserialize_1_i16s (a b: i16) =
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 b b b b b b b b a a a a a a a a
  in
  let coefficients_in_msb:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (mk_i16 1 <<! mk_i32 8 <: i16)
          (mk_i16 1 <<! mk_i32 9 <: i16) (mk_i16 1 <<! mk_i32 10 <: i16)
          (mk_i16 1 <<! mk_i32 11 <: i16) (mk_i16 1 <<! mk_i32 12 <: i16)
          (mk_i16 1 <<! mk_i32 13 <: i16) (mk_i16 1 <<! mk_i32 14 <: i16) (mk_i16 (-32768))
          (mk_i16 1 <<! mk_i32 8 <: i16) (mk_i16 1 <<! mk_i32 9 <: i16)
          (mk_i16 1 <<! mk_i32 10 <: i16) (mk_i16 1 <<! mk_i32 11 <: i16)
          (mk_i16 1 <<! mk_i32 12 <: i16) (mk_i16 1 <<! mk_i32 13 <: i16)
          (mk_i16 1 <<! mk_i32 14 <: i16) (mk_i16 (-32768))
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_srli_epi16 (mk_i32 15) coefficients_in_msb

#pop-options

[@@"opaque_to_smt"]

let deserialize_1___deserialize_1_u8s (a b: u8) =
  deserialize_1___deserialize_1_i16s (cast (a <: u8) <: i16) (cast (b <: u8) <: i16)

#restart-solver

let deserialize_1_ (bytes: t_Slice u8) =
  deserialize_1___deserialize_1_u8s (bytes.[ mk_usize 0 ] <: u8) (bytes.[ mk_usize 1 ] <: u8)

#push-options "--ext context_pruning --split_queries always"

let serialize_4_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let serialized:t_Array u8 (mk_usize 16) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 16) in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    mm256_concat_pairs_n (mk_u8 4) vector
  in
  let adjacent_8_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 adjacent_2_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 12) (mk_i8 8) (mk_i8 4) (mk_i8 0) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 12) (mk_i8 8) (mk_i8 4)
          (mk_i8 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permutevar8x32_epi32 adjacent_8_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 4)
          (mk_i32 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let combined:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 combined
  in
  let serialized:t_Array u8 (mk_usize 16) =
    Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 serialized combined
  in
  let _:Prims.unit =
    assert (forall (i: nat{i < 64}). combined i == bit_vec_of_int_t_array serialized 8 i);
    introduce forall (i: nat{i < 64}) . combined i = vector ((i / 4) * 16 + i % 4)
    with assert_norm (BitVec.Utils.forall64 (fun i -> combined i = vector ((i / 4) * 16 + i % 4)));
    assert (forall (i: nat{i < 64}).
          bit_vec_of_int_t_array serialized 8 i == vector ((i / 4) * 16 + i % 4))
  in
  Core.Result.impl__unwrap #(t_Array u8 (mk_usize 8))
    #Core.Array.t_TryFromSliceError
    (Core.Convert.f_try_into #(t_Slice u8)
        #(t_Array u8 (mk_usize 8))
        #FStar.Tactics.Typeclasses.solve
        (serialized.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 8 }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result (t_Array u8 (mk_usize 8)) Core.Array.t_TryFromSliceError)

#pop-options

[@@"opaque_to_smt"]

let deserialize_4___deserialize_4_i16s (b0 b1 b2 b3 b4 b5 b6 b7: i16) =
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 b7 b7 b6 b6 b5 b5 b4 b4 b3 b3 b2 b2 b1 b1 b0 b0
  in
  let coefficients_in_msb:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 4 <: i16)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let coefficients_in_lsb:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi16 (mk_i32 4) coefficients_in_msb
  in
  Libcrux_intrinsics.Avx2_extract.mm256_and_si256 coefficients_in_lsb
    (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 ((mk_i16 1 <<! mk_i32 4 <: i16) -! mk_i16 1
          <:
          i16)
      <:
      Libcrux_intrinsics.Avx2_extract.t_Vec256)

[@@"opaque_to_smt"]

let deserialize_4___deserialize_4_u8s (b0 b1 b2 b3 b4 b5 b6 b7: u8) =
  deserialize_4___deserialize_4_i16s (cast (b0 <: u8) <: i16)
    (cast (b1 <: u8) <: i16)
    (cast (b2 <: u8) <: i16)
    (cast (b3 <: u8) <: i16)
    (cast (b4 <: u8) <: i16)
    (cast (b5 <: u8) <: i16)
    (cast (b6 <: u8) <: i16)
    (cast (b7 <: u8) <: i16)

#restart-solver

let deserialize_4_ (bytes: t_Slice u8) =
  deserialize_4___deserialize_4_u8s (bytes.[ mk_usize 0 ] <: u8)
    (bytes.[ mk_usize 1 ] <: u8)
    (bytes.[ mk_usize 2 ] <: u8)
    (bytes.[ mk_usize 3 ] <: u8)
    (bytes.[ mk_usize 4 ] <: u8)
    (bytes.[ mk_usize 5 ] <: u8)
    (bytes.[ mk_usize 6 ] <: u8)
    (bytes.[ mk_usize 7 ] <: u8)

let serialize_5_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let serialized:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_madd_epi16 vector
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (mk_i16 1 <<! mk_i32 5 <: i16) (mk_i16 1)
          (mk_i16 1 <<! mk_i32 5 <: i16) (mk_i16 1) (mk_i16 1 <<! mk_i32 5 <: i16) (mk_i16 1)
          (mk_i16 1 <<! mk_i32 5 <: i16) (mk_i16 1) (mk_i16 1 <<! mk_i32 5 <: i16) (mk_i16 1)
          (mk_i16 1 <<! mk_i32 5 <: i16) (mk_i16 1) (mk_i16 1 <<! mk_i32 5 <: i16) (mk_i16 1)
          (mk_i16 1 <<! mk_i32 5 <: i16) (mk_i16 1)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 adjacent_2_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (mk_i32 0)
          (mk_i32 22)
          (mk_i32 0)
          (mk_i32 22)
          (mk_i32 0)
          (mk_i32 22)
          (mk_i32 0)
          (mk_i32 22)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 (mk_i32 22) adjacent_4_combined
  in
  let adjacent_8_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (mk_i32 8) adjacent_4_combined
  in
  let adjacent_8_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 adjacent_8_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 12)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 12)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_8_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 (mk_i32 12) adjacent_8_combined
  in
  let lower_8_:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 adjacent_8_combined
  in
  let serialized:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = mk_usize 16
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          lower_8_
        <:
        t_Slice u8)
  in
  let upper_8_:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 (mk_i32 1) adjacent_8_combined
  in
  let serialized:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = mk_usize 5; Core.Ops.Range.f_end = mk_usize 21 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = mk_usize 5;
                Core.Ops.Range.f_end = mk_usize 21
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          upper_8_
        <:
        t_Slice u8)
  in
  Core.Result.impl__unwrap #(t_Array u8 (mk_usize 10))
    #Core.Array.t_TryFromSliceError
    (Core.Convert.f_try_into #(t_Slice u8)
        #(t_Array u8 (mk_usize 10))
        #FStar.Tactics.Typeclasses.solve
        (serialized.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 10 }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result (t_Array u8 (mk_usize 10)) Core.Array.t_TryFromSliceError)

#push-options "--ext context_pruning --split_queries always"

let serialize_10___serialize_10_vec (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    mm256_concat_pairs_n (mk_u8 10) vector
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 adjacent_2_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (mk_i32 0)
          (mk_i32 12)
          (mk_i32 0)
          (mk_i32 12)
          (mk_i32 0)
          (mk_i32 12)
          (mk_i32 0)
          (mk_i32 12)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 (mk_i32 12) adjacent_4_combined
  in
  let adjacent_8_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 adjacent_4_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 12) (mk_i8 11) (mk_i8 10) (mk_i8 9)
          (mk_i8 8) (mk_i8 4) (mk_i8 3) (mk_i8 2) (mk_i8 1) (mk_i8 0) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 12) (mk_i8 11) (mk_i8 10)
          (mk_i8 9) (mk_i8 8) (mk_i8 4) (mk_i8 3) (mk_i8 2) (mk_i8 1) (mk_i8 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let lower_8_:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 adjacent_8_combined
  in
  let upper_8_:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 (mk_i32 1) adjacent_8_combined
  in
  let _:Prims.unit =
    introduce forall (i: nat{i < 80}) . lower_8_ i = vector ((i / 10) * 16 + i % 10)
    with assert_norm (BitVec.Utils.forall_n 80
          (fun i -> lower_8_ i = vector ((i / 10) * 16 + i % 10)));
    introduce forall (i: nat{i < 80}) . upper_8_ i = vector (128 + (i / 10) * 16 + i % 10)
    with assert_norm (BitVec.Utils.forall_n 80
          (fun i -> upper_8_ i = vector (128 + (i / 10) * 16 + i % 10)))
  in
  lower_8_, upper_8_
  <:
  (Libcrux_intrinsics.Avx2_extract.t_Vec128 & Libcrux_intrinsics.Avx2_extract.t_Vec128)

#pop-options

#push-options "--ext context_pruning --split_queries always"

let serialize_10_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let lower_8_, upper_8_:(Libcrux_intrinsics.Avx2_extract.t_Vec128 &
    Libcrux_intrinsics.Avx2_extract.t_Vec128) =
    serialize_10___serialize_10_vec vector
  in
  let serialized:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let serialized:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = mk_usize 16
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          lower_8_
        <:
        t_Slice u8)
  in
  let serialized:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = mk_usize 10; Core.Ops.Range.f_end = mk_usize 26 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = mk_usize 10;
                Core.Ops.Range.f_end = mk_usize 26
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          upper_8_
        <:
        t_Slice u8)
  in
  Core.Result.impl__unwrap #(t_Array u8 (mk_usize 20))
    #Core.Array.t_TryFromSliceError
    (Core.Convert.f_try_into #(t_Slice u8)
        #(t_Array u8 (mk_usize 20))
        #FStar.Tactics.Typeclasses.solve
        (serialized.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 20 }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result (t_Array u8 (mk_usize 20)) Core.Array.t_TryFromSliceError)

#pop-options

#push-options "--admit_smt_queries true"

let serialize_11_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let array:t_Array i16 (mk_usize 16) = Rust_primitives.Hax.repeat (mk_i16 0) (mk_usize 16) in
  let array:t_Array i16 (mk_usize 16) =
    Libcrux_intrinsics.Avx2_extract.mm256_storeu_si256_i16 array vector
  in
  let input:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Traits.f_from_i16_array #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      (array <: t_Slice i16)
  in
  Libcrux_ml_kem.Vector.Traits.f_serialize_11_ #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
    #FStar.Tactics.Typeclasses.solve
    input

#pop-options

#push-options "--admit_smt_queries true"

let deserialize_11_ (bytes: t_Slice u8) =
  let output:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Traits.f_deserialize_11_ #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      bytes
  in
  let array:t_Array i16 (mk_usize 16) =
    Libcrux_ml_kem.Vector.Traits.f_to_i16_array #Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      #FStar.Tactics.Typeclasses.solve
      output
  in
  Libcrux_intrinsics.Avx2_extract.mm256_loadu_si256_i16 (array <: t_Slice i16)

#pop-options

#push-options "--ext context_pruning --split_queries always"

let serialize_12___serialize_12_vec (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let adjacent_2_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    mm256_concat_pairs_n (mk_u8 12) vector
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sllv_epi32 adjacent_2_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (mk_i32 0)
          (mk_i32 8)
          (mk_i32 0)
          (mk_i32 8)
          (mk_i32 0)
          (mk_i32 8)
          (mk_i32 0)
          (mk_i32 8)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let adjacent_4_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 (mk_i32 8) adjacent_4_combined
  in
  let adjacent_8_combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 adjacent_4_combined
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 13) (mk_i8 12) (mk_i8 11) (mk_i8 10) (mk_i8 9) (mk_i8 8) (mk_i8 5)
          (mk_i8 4) (mk_i8 3) (mk_i8 2) (mk_i8 1) (mk_i8 0) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 13) (mk_i8 12) (mk_i8 11) (mk_i8 10) (mk_i8 9) (mk_i8 8) (mk_i8 5)
          (mk_i8 4) (mk_i8 3) (mk_i8 2) (mk_i8 1) (mk_i8 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let lower_8_:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 adjacent_8_combined
  in
  let upper_8_:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 (mk_i32 1) adjacent_8_combined
  in
  let _:Prims.unit =
    introduce forall (i: nat{i < 96}) . lower_8_ i = vector ((i / 12) * 16 + i % 12)
    with assert_norm (BitVec.Utils.forall_n 96
          (fun i -> lower_8_ i = vector ((i / 12) * 16 + i % 12)));
    introduce forall (i: nat{i < 96}) . upper_8_ i = vector (128 + (i / 12) * 16 + i % 12)
    with assert_norm (BitVec.Utils.forall_n 96
          (fun i -> upper_8_ i = vector (128 + (i / 12) * 16 + i % 12)))
  in
  lower_8_, upper_8_
  <:
  (Libcrux_intrinsics.Avx2_extract.t_Vec128 & Libcrux_intrinsics.Avx2_extract.t_Vec128)

#pop-options

#push-options "--ext context_pruning --split_queries always"

let serialize_12_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let serialized:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let lower_8_, upper_8_:(Libcrux_intrinsics.Avx2_extract.t_Vec128 &
    Libcrux_intrinsics.Avx2_extract.t_Vec128) =
    serialize_12___serialize_12_vec vector
  in
  let serialized:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = mk_usize 16
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          lower_8_
        <:
        t_Slice u8)
  in
  let serialized:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({ Core.Ops.Range.f_start = mk_usize 12; Core.Ops.Range.f_end = mk_usize 28 }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_bytes_si128 (serialized.[ {
                Core.Ops.Range.f_start = mk_usize 12;
                Core.Ops.Range.f_end = mk_usize 28
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          upper_8_
        <:
        t_Slice u8)
  in
  Core.Result.impl__unwrap #(t_Array u8 (mk_usize 24))
    #Core.Array.t_TryFromSliceError
    (Core.Convert.f_try_into #(t_Slice u8)
        #(t_Array u8 (mk_usize 24))
        #FStar.Tactics.Typeclasses.solve
        (serialized.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 24 }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result (t_Array u8 (mk_usize 24)) Core.Array.t_TryFromSliceError)

#pop-options

let deserialize_5_ (bytes: t_Slice u8) =
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_set_epi8 (bytes.[ mk_usize 9 ] <: u8)
      (bytes.[ mk_usize 8 ] <: u8) (bytes.[ mk_usize 8 ] <: u8) (bytes.[ mk_usize 7 ] <: u8)
      (bytes.[ mk_usize 7 ] <: u8) (bytes.[ mk_usize 6 ] <: u8) (bytes.[ mk_usize 6 ] <: u8)
      (bytes.[ mk_usize 5 ] <: u8) (bytes.[ mk_usize 4 ] <: u8) (bytes.[ mk_usize 3 ] <: u8)
      (bytes.[ mk_usize 3 ] <: u8) (bytes.[ mk_usize 2 ] <: u8) (bytes.[ mk_usize 2 ] <: u8)
      (bytes.[ mk_usize 1 ] <: u8) (bytes.[ mk_usize 1 ] <: u8) (bytes.[ mk_usize 0 ] <: u8)
  in
  let coefficients_loaded:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    mm256_si256_from_two_si128 coefficients coefficients
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 coefficients_loaded
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (mk_i8 15) (mk_i8 14) (mk_i8 15) (mk_i8 14)
          (mk_i8 13) (mk_i8 12) (mk_i8 13) (mk_i8 12) (mk_i8 11) (mk_i8 10) (mk_i8 11) (mk_i8 10)
          (mk_i8 9) (mk_i8 8) (mk_i8 9) (mk_i8 8) (mk_i8 7) (mk_i8 6) (mk_i8 7) (mk_i8 6) (mk_i8 5)
          (mk_i8 4) (mk_i8 5) (mk_i8 4) (mk_i8 3) (mk_i8 2) (mk_i8 3) (mk_i8 2) (mk_i8 1) (mk_i8 0)
          (mk_i8 1) (mk_i8 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 5 <: i16) (mk_i16 1 <<! mk_i32 2 <: i16)
          (mk_i16 1 <<! mk_i32 7 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16)
          (mk_i16 1 <<! mk_i32 9 <: i16) (mk_i16 1 <<! mk_i32 6 <: i16)
          (mk_i16 1 <<! mk_i32 11 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 5 <: i16) (mk_i16 1 <<! mk_i32 2 <: i16)
          (mk_i16 1 <<! mk_i32 7 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16)
          (mk_i16 1 <<! mk_i32 9 <: i16) (mk_i16 1 <<! mk_i32 6 <: i16)
          (mk_i16 1 <<! mk_i32 11 <: i16)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_srli_epi16 (mk_i32 11) coefficients

[@@"opaque_to_smt"]

let deserialize_10___deserialize_10_vec
      (lower_coefficients0 upper_coefficients0: Libcrux_intrinsics.Avx2_extract.t_Vec128)
     =
  let lower_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_shuffle_epi8 lower_coefficients0
      (Libcrux_intrinsics.Avx2_extract.mm_set_epi8 (mk_u8 9) (mk_u8 8) (mk_u8 8) (mk_u8 7) (mk_u8 7)
          (mk_u8 6) (mk_u8 6) (mk_u8 5) (mk_u8 4) (mk_u8 3) (mk_u8 3) (mk_u8 2) (mk_u8 2) (mk_u8 1)
          (mk_u8 1) (mk_u8 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
  in
  let upper_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_shuffle_epi8 upper_coefficients0
      (Libcrux_intrinsics.Avx2_extract.mm_set_epi8 (mk_u8 15) (mk_u8 14) (mk_u8 14) (mk_u8 13)
          (mk_u8 13) (mk_u8 12) (mk_u8 12) (mk_u8 11) (mk_u8 10) (mk_u8 9) (mk_u8 9) (mk_u8 8)
          (mk_u8 8) (mk_u8 7) (mk_u8 7) (mk_u8 6)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    mm256_si256_from_two_si128 lower_coefficients upper_coefficients
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 2 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16)
          (mk_i16 1 <<! mk_i32 6 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 2 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16)
          (mk_i16 1 <<! mk_i32 6 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 2 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16)
          (mk_i16 1 <<! mk_i32 6 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 2 <: i16) (mk_i16 1 <<! mk_i32 4 <: i16)
          (mk_i16 1 <<! mk_i32 6 <: i16)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi16 (mk_i32 6) coefficients
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 ((mk_i16 1 <<! mk_i32 10 <: i16) -! mk_i16 1
            <:
            i16)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let _:Prims.unit =
    assert_norm (BitVec.Utils.forall256 (fun i ->
              coefficients i =
              (if i % 16 < 10
                then
                  let j = (i / 16) * 10 + i % 16 in
                  if i < 128 then lower_coefficients0 j else upper_coefficients0 (j - 32)
                else 0)))
  in
  coefficients

let deserialize_10_ (bytes: t_Slice u8) =
  let lower_coefficients:t_Slice u8 =
    bytes.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 16 }
      <:
      Core.Ops.Range.t_Range usize ]
  in
  let upper_coefficients:t_Slice u8 =
    bytes.[ { Core.Ops.Range.f_start = mk_usize 4; Core.Ops.Range.f_end = mk_usize 20 }
      <:
      Core.Ops.Range.t_Range usize ]
  in
  deserialize_10___deserialize_10_vec (Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 lower_coefficients

      <:
      Libcrux_intrinsics.Avx2_extract.t_Vec128)
    (Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 upper_coefficients
      <:
      Libcrux_intrinsics.Avx2_extract.t_Vec128)

[@@"opaque_to_smt"]

let deserialize_12___deserialize_12_vec
      (lower_coefficients0 upper_coefficients0: Libcrux_intrinsics.Avx2_extract.t_Vec128)
     =
  let lower_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_shuffle_epi8 lower_coefficients0
      (Libcrux_intrinsics.Avx2_extract.mm_set_epi8 (mk_u8 11) (mk_u8 10) (mk_u8 10) (mk_u8 9)
          (mk_u8 8) (mk_u8 7) (mk_u8 7) (mk_u8 6) (mk_u8 5) (mk_u8 4) (mk_u8 4) (mk_u8 3) (mk_u8 2)
          (mk_u8 1) (mk_u8 1) (mk_u8 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
  in
  let upper_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_shuffle_epi8 upper_coefficients0
      (Libcrux_intrinsics.Avx2_extract.mm_set_epi8 (mk_u8 15) (mk_u8 14) (mk_u8 14) (mk_u8 13)
          (mk_u8 12) (mk_u8 11) (mk_u8 11) (mk_u8 10) (mk_u8 9) (mk_u8 8) (mk_u8 8) (mk_u8 7)
          (mk_u8 6) (mk_u8 5) (mk_u8 5) (mk_u8 4)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    mm256_si256_from_two_si128 lower_coefficients upper_coefficients
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 4 <: i16)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi16 (mk_i32 4) coefficients
  in
  let coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 coefficients
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 ((mk_i16 1 <<! mk_i32 12 <: i16) -! mk_i16 1
            <:
            i16)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let _:Prims.unit =
    assert_norm (BitVec.Utils.forall256 (fun i ->
              coefficients i =
              (if i % 16 < 12
                then
                  let j = (i / 16) * 12 + i % 16 in
                  if i < 128 then lower_coefficients0 j else upper_coefficients0 (j - 64)
                else 0)))
  in
  coefficients

let deserialize_12_ (bytes: t_Slice u8) =
  let lower_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 (bytes.[ {
            Core.Ops.Range.f_start = mk_usize 0;
            Core.Ops.Range.f_end = mk_usize 16
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let upper_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 (bytes.[ {
            Core.Ops.Range.f_start = mk_usize 8;
            Core.Ops.Range.f_end = mk_usize 24
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  deserialize_12___deserialize_12_vec lower_coefficients upper_coefficients
