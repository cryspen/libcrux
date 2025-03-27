module Libcrux_ml_dsa.Simd.Portable.Encoding.Commitment
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let serialize_4_
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
            forall (i: nat{i < 8 * 4}). inp i == out i)) =
  let coefficient0:u8 =
    cast (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 0 ] <: i32) <: u8
  in
  let coefficient1:u8 =
    cast (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 1 ] <: i32) <: u8
  in
  let coefficient2:u8 =
    cast (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 2 ] <: i32) <: u8
  in
  let coefficient3:u8 =
    cast (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 3 ] <: i32) <: u8
  in
  let coefficient4:u8 =
    cast (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 4 ] <: i32) <: u8
  in
  let coefficient5:u8 =
    cast (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 5 ] <: i32) <: u8
  in
  let coefficient6:u8 =
    cast (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 6 ] <: i32) <: u8
  in
  let coefficient7:u8 =
    cast (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 7 ] <: i32) <: u8
  in
  let byte0:u8 = (coefficient1 <<! mk_i32 4 <: u8) |. coefficient0 in
  let byte1:u8 = (coefficient3 <<! mk_i32 4 <: u8) |. coefficient2 in
  let byte2:u8 = (coefficient5 <<! mk_i32 4 <: u8) |. coefficient4 in
  let byte3:u8 = (coefficient7 <<! mk_i32 4 <: u8) |. coefficient6 in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized (mk_usize 0) byte0
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized (mk_usize 1) byte1
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized (mk_usize 2) byte2
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized (mk_usize 3) byte3
  in
  serialized

let serialize_6_
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
            forall (i: nat{i < 8 * 6}). inp i == out i)) =
  let coefficient0:u8 =
    cast (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 0 ] <: i32) <: u8
  in
  let coefficient1:u8 =
    cast (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 1 ] <: i32) <: u8
  in
  let coefficient2:u8 =
    cast (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 2 ] <: i32) <: u8
  in
  let coefficient3:u8 =
    cast (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 3 ] <: i32) <: u8
  in
  let coefficient4:u8 =
    cast (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 4 ] <: i32) <: u8
  in
  let coefficient5:u8 =
    cast (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 5 ] <: i32) <: u8
  in
  let coefficient6:u8 =
    cast (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 6 ] <: i32) <: u8
  in
  let coefficient7:u8 =
    cast (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 7 ] <: i32) <: u8
  in
  let byte0:u8 = (coefficient1 <<! mk_i32 6 <: u8) |. coefficient0 in
  let byte1:u8 = (coefficient2 <<! mk_i32 4 <: u8) |. (coefficient1 >>! mk_i32 2 <: u8) in
  let byte2:u8 = (coefficient3 <<! mk_i32 2 <: u8) |. (coefficient2 >>! mk_i32 4 <: u8) in
  let byte3:u8 = (coefficient5 <<! mk_i32 6 <: u8) |. coefficient4 in
  let byte4:u8 = (coefficient6 <<! mk_i32 4 <: u8) |. (coefficient5 >>! mk_i32 2 <: u8) in
  let byte5:u8 = (coefficient7 <<! mk_i32 2 <: u8) |. (coefficient6 >>! mk_i32 4 <: u8) in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized (mk_usize 0) byte0
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized (mk_usize 1) byte1
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized (mk_usize 2) byte2
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized (mk_usize 3) byte3
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized (mk_usize 4) byte4
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized (mk_usize 5) byte5
  in
  serialized

let serialize
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
              forall (i: nat{i < 8 * d}). inp i == out i))) =
  let serialized:t_Slice u8 =
    match cast (Core.Slice.impl__len #u8 serialized <: usize) <: u8 with
    | Rust_primitives.Integers.MkInt 4 -> serialize_4_ simd_unit serialized
    | Rust_primitives.Integers.MkInt 6 -> serialize_6_ simd_unit serialized
    | _ -> serialized
  in
  serialized
