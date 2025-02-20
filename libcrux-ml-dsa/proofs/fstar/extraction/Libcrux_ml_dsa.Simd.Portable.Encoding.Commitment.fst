module Libcrux_ml_dsa.Simd.Portable.Encoding.Commitment
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let serialize_4_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
     =
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
     =
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
     =
  let serialized:t_Slice u8 =
    match cast (Core.Slice.impl__len #u8 serialized <: usize) <: u8 with
    | Rust_primitives.Integers.MkInt 4 -> serialize_4_ simd_unit serialized
    | Rust_primitives.Integers.MkInt 6 -> serialize_6_ simd_unit serialized
    | _ -> serialized
  in
  serialized
