module Libcrux_ml_dsa.Simd.Avx2.Encoding.Commitment
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

[@@FStar.Tactics.postprocess_with Core_models.Abstractions.Bitvec.bitvec_postprocess_norm]

let serialize_6___normalized_serialize_6_
      (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) &
      Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) =
  let adjacent_2_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sllv_epi32 simd_unit
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 26)
          (mk_i32 0)
          (mk_i32 26)
          (mk_i32 0)
          (mk_i32 26)
          (mk_i32 0)
          (mk_i32 26)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_2_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srli_epi64 (mk_i32 26) adjacent_2_combined
  in
  let adjacent_3_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_shuffle_epi8 adjacent_2_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi8 (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 9) (mk_i8 8) (mk_i8 1) (mk_i8 0) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1))
          (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 (-1)) (mk_i8 9) (mk_i8 8) (mk_i8 1) (mk_i8 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_3_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_mullo_epi16 adjacent_3_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi16 (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 4 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 0 <: i16) (mk_i16 1 <<! mk_i32 0 <: i16)
          (mk_i16 1 <<! mk_i32 4 <: i16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_3_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srlv_epi32 adjacent_3_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 4)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 4)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let lower:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm256_castsi256_si128 adjacent_3_combined
  in
  let upper:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm256_extracti128_si256 (mk_i32 1) adjacent_3_combined
  in
  lower, upper
  <:
  (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) &
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))

let serialize_6_ (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure
      (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) &
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
      Prims.l_True
      (ensures
        fun temp_0_ ->
          let lower, upper:(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) &
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) =
            temp_0_
          in
          let lower:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
            Core.Convert.f_from #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
              #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
              #FStar.Tactics.Typeclasses.solve
              lower
          in
          let upper:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
            Core.Convert.f_from #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
              #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
              #FStar.Tactics.Typeclasses.solve
              upper
          in
          let simd_unit:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
            Core.Convert.f_from #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
              #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
              #FStar.Tactics.Typeclasses.solve
              simd_unit
          in
          forall (i: u64).
            b2t (i <. mk_u64 48 <: bool) ==>
            b2t
            ((if i <. mk_u64 24 <: bool
                then lower.[ i ] <: Core_models.Abstractions.Bit.t_Bit
                else upper.[ i -! mk_u64 24 <: u64 ] <: Core_models.Abstractions.Bit.t_Bit) =.
              (simd_unit.[ ((i /! mk_u64 6 <: u64) *! mk_u64 32 <: u64) +! (i %! mk_u64 6 <: u64)
                  <:
                  u64 ]
                <:
                Core_models.Abstractions.Bit.t_Bit)
              <:
              bool)) = serialize_6___normalized_serialize_6_ simd_unit

[@@FStar.Tactics.postprocess_with Core_models.Abstractions.Bitvec.bitvec_postprocess_norm]

let serialize_4___normalized_serialize_4_
      (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  let adjacent_2_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_sllv_epi32 simd_unit
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 28)
          (mk_i32 0)
          (mk_i32 28)
          (mk_i32 0)
          (mk_i32 28)
          (mk_i32 0)
          (mk_i32 28)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_2_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_srli_epi64 (mk_i32 28) adjacent_2_combined
  in
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Libcrux_intrinsics.Avx2.mm256_permutevar8x32_epi32 adjacent_2_combined
      (Libcrux_intrinsics.Avx2.mm256_set_epi32 (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 0)
          (mk_i32 6)
          (mk_i32 2)
          (mk_i32 4)
          (mk_i32 0)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let adjacent_4_combined:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
    Libcrux_intrinsics.Avx2.mm256_castsi256_si128 adjacent_4_combined
  in
  Libcrux_intrinsics.Avx2.mm_shuffle_epi8 adjacent_4_combined
    (Libcrux_intrinsics.Avx2.mm_set_epi8 (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240)
        (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240) (mk_u8 240)
        (mk_u8 12) (mk_u8 4) (mk_u8 8) (mk_u8 0)
      <:
      Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))

let serialize_4_ (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Prims.Pure (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
      Prims.l_True
      (ensures
        fun r ->
          let r:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) = r in
          let r:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
            Core.Convert.f_from #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
              #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
              #FStar.Tactics.Typeclasses.solve
              r
          in
          let simd_unit:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
            Core.Convert.f_from #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
              #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
              #FStar.Tactics.Typeclasses.solve
              simd_unit
          in
          forall (i: u64).
            b2t (i <. mk_u64 32 <: bool) ==>
            b2t
            ((r.[ i ] <: Core_models.Abstractions.Bit.t_Bit) =.
              (simd_unit.[ ((i /! mk_u64 4 <: u64) *! mk_u64 32 <: u64) +! (i %! mk_u64 4 <: u64)
                  <:
                  u64 ]
                <:
                Core_models.Abstractions.Bit.t_Bit)
              <:
              bool)) = serialize_4___normalized_serialize_4_ simd_unit

let serialize (simd_unit: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (Core.Slice.impl__len #u8 out <: usize) =. mk_usize 4 ||
        (Core.Slice.impl__len #u8 out <: usize) =. mk_usize 6)
      (fun _ -> Prims.l_True) =
  let serialized:t_Array u8 (mk_usize 19) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 19) in
  let out, serialized:(t_Slice u8 & t_Array u8 (mk_usize 19)) =
    match cast (Core.Slice.impl__len #u8 out <: usize) <: u8 with
    | Rust_primitives.Integers.MkInt 4 ->
      let serialized:t_Array u8 (mk_usize 19) =
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
              (serialize_4_ simd_unit <: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
            <:
            t_Slice u8)
      in
      let out:t_Slice u8 =
        Core.Slice.impl__copy_from_slice #u8
          out
          (serialized.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 4 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
      in
      out, serialized <: (t_Slice u8 & t_Array u8 (mk_usize 19))
    | Rust_primitives.Integers.MkInt 6 ->
      let lower_3_, upper_3_:(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) &
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) =
        serialize_6_ simd_unit
      in
      let serialized:t_Array u8 (mk_usize 19) =
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
              lower_3_
            <:
            t_Slice u8)
      in
      let serialized:t_Array u8 (mk_usize 19) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
          ({ Core.Ops.Range.f_start = mk_usize 3; Core.Ops.Range.f_end = mk_usize 19 }
            <:
            Core.Ops.Range.t_Range usize)
          (Libcrux_intrinsics.Avx2.mm_storeu_bytes_si128 (serialized.[ {
                    Core.Ops.Range.f_start = mk_usize 3;
                    Core.Ops.Range.f_end = mk_usize 19
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              upper_3_
            <:
            t_Slice u8)
      in
      let out:t_Slice u8 =
        Core.Slice.impl__copy_from_slice #u8
          out
          (serialized.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 6 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
      in
      out, serialized <: (t_Slice u8 & t_Array u8 (mk_usize 19))
    | _ -> out, serialized <: (t_Slice u8 & t_Array u8 (mk_usize 19))
  in
  out
