module Libcrux_ml_dsa.Simd.Portable.Encoding.Commitment
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val serialize_4_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        Seq.length serialized == 4 /\
        (forall i.
            bounded (Seq.index simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values i) 4))
      (ensures
        fun serialized_future ->
          let serialized_future:t_Slice u8 = serialized_future in
          let serialized_future:t_Slice u8 = serialized_future in
          Seq.length serialized_future == Seq.length serialized /\
          (let inp =
              bit_vec_of_int_t_array #I32
                #(mk_usize 8)
                simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                4
            in
            let out = bit_vec_of_int_t_array #U8 #(mk_usize 4) serialized_future 8 in
            forall (i: nat{i < 8 * 4}). inp i == out i))

val serialize_6_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        Seq.length serialized == 6 /\
        (forall i.
            bounded (Seq.index simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values i) 6))
      (ensures
        fun serialized_future ->
          let serialized_future:t_Slice u8 = serialized_future in
          let serialized_future:t_Slice u8 = serialized_future in
          Seq.length serialized_future == Seq.length serialized /\
          (let inp =
              bit_vec_of_int_t_array #I32
                #(mk_usize 8)
                simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                6
            in
            let out = bit_vec_of_int_t_array #U8 #(mk_usize 6) serialized_future 8 in
            forall (i: nat{i < 8 * 6}). inp i == out i))

val serialize
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (let d = Seq.length serialized in
          (d == 4 \/ d == 6) /\
          (forall i.
              bounded (Seq.index simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values i) d)))
      (ensures
        fun serialized_future ->
          let serialized_future:t_Slice u8 = serialized_future in
          let serialized_future:t_Slice u8 = serialized_future in
          let d = Seq.length serialized in
          (Seq.length serialized_future == d /\
            (let inp =
                bit_vec_of_int_t_array #I32
                  #(mk_usize 8)
                  simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                  d
              in
              let out = bit_vec_of_int_t_array #U8 #(mk_usize d) serialized_future 8 in
              forall (i: nat{i < 8 * d}). inp i == out i)))
