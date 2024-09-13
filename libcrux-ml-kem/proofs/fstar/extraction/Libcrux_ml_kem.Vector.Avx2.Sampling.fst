module Libcrux_ml_kem.Vector.Avx2.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

#push-options "--admit_smt_queries true"

let rejection_sample (input: t_Slice u8) (output: t_Slice i16) =
  let field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
  in
  let potential_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_kem.Vector.Avx2.Serialize.deserialize_12_ input
  in
  let compare_with_field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_cmpgt_epi16 field_modulus potential_coefficients
  in
  let good:t_Array u8 (sz 2) =
    Libcrux_ml_kem.Vector.Avx2.Serialize.serialize_1_ compare_with_field_modulus
  in
  let _:Prims.unit =
    assert (v (cast (good.[ sz 0 ] <: u8) <: usize) < 256);
    assert (v (cast (good.[ sz 1 ] <: u8) <: usize) < 256);
    assume (v (cast (Core.Num.impl__u8__count_ones good.[ sz 0 ]) <: usize) <= 8);
    assume (v (cast (Core.Num.impl__u8__count_ones good.[ sz 1 ]) <: usize) <= 8);
    assume (Core.Ops.Index.f_index_pre output
          ({
              Core.Ops.Range.f_start = cast (Core.Num.impl__u8__count_ones good.[ sz 0 ]) <: usize;
              Core.Ops.Range.f_end
              =
              (cast (Core.Num.impl__u8__count_ones good.[ sz 0 ]) <: usize) +! sz 8
            }))
  in
  let lower_shuffles:t_Array u8 (sz 16) =
    Libcrux_ml_kem.Vector.Rej_sample_table.v_REJECTION_SAMPLE_SHUFFLE_TABLE.[ cast (good.[ sz 0 ]
          <:
          u8)
      <:
      usize ]
  in
  let lower_shuffles:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 (lower_shuffles <: t_Slice u8)
  in
  let lower_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 potential_coefficients
  in
  let lower_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_shuffle_epi8 lower_coefficients lower_shuffles
  in
  let output:t_Slice i16 =
    Libcrux_intrinsics.Avx2_extract.mm_storeu_si128 output lower_coefficients
  in
  let sampled_count:usize =
    cast (Core.Num.impl__u8__count_ones (good.[ sz 0 ] <: u8) <: u32) <: usize
  in
  let upper_shuffles:t_Array u8 (sz 16) =
    Libcrux_ml_kem.Vector.Rej_sample_table.v_REJECTION_SAMPLE_SHUFFLE_TABLE.[ cast (good.[ sz 1 ]
          <:
          u8)
      <:
      usize ]
  in
  let upper_shuffles:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_loadu_si128 (upper_shuffles <: t_Slice u8)
  in
  let upper_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 1l potential_coefficients
  in
  let upper_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_shuffle_epi8 upper_coefficients upper_shuffles
  in
  let output:t_Slice i16 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range output
      ({
          Core.Ops.Range.f_start = sampled_count;
          Core.Ops.Range.f_end = sampled_count +! sz 8 <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Libcrux_intrinsics.Avx2_extract.mm_storeu_si128 (output.[ {
                Core.Ops.Range.f_start = sampled_count;
                Core.Ops.Range.f_end = sampled_count +! sz 8 <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice i16)
          upper_coefficients
        <:
        t_Slice i16)
  in
  let hax_temp_output:usize =
    sampled_count +! (cast (Core.Num.impl__u8__count_ones (good.[ sz 1 ] <: u8) <: u32) <: usize)
  in
  output, hax_temp_output <: (t_Slice i16 & usize)

#pop-options
