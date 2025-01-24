module Libcrux_ml_dsa.Simd.Portable.Encoding.T0
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let change_t0_interval (t0: i32) =
  (1l <<! (Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T -! sz 1 <: usize) <: i32) -! t0

let serialize
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. sz 13 <: bool)
      in
      ()
  in
  let coefficient0:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ sz 0 ] <: i32)
  in
  let coefficient1:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ sz 1 ] <: i32)
  in
  let coefficient2:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ sz 2 ] <: i32)
  in
  let coefficient3:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ sz 3 ] <: i32)
  in
  let coefficient4:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ sz 4 ] <: i32)
  in
  let coefficient5:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ sz 5 ] <: i32)
  in
  let coefficient6:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ sz 6 ] <: i32)
  in
  let coefficient7:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ sz 7 ] <: i32)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 0)
      (cast (coefficient0 <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 1)
      (cast (coefficient0 >>! 8l <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 1)
      ((serialized.[ sz 1 ] <: u8) |. (cast (coefficient1 <<! 5l <: i32) <: u8) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 2)
      (cast (coefficient1 >>! 3l <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 3)
      (cast (coefficient1 >>! 11l <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 3)
      ((serialized.[ sz 3 ] <: u8) |. (cast (coefficient2 <<! 2l <: i32) <: u8) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 4)
      (cast (coefficient2 >>! 6l <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 4)
      ((serialized.[ sz 4 ] <: u8) |. (cast (coefficient3 <<! 7l <: i32) <: u8) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 5)
      (cast (coefficient3 >>! 1l <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 6)
      (cast (coefficient3 >>! 9l <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 6)
      ((serialized.[ sz 6 ] <: u8) |. (cast (coefficient4 <<! 4l <: i32) <: u8) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 7)
      (cast (coefficient4 >>! 4l <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 8)
      (cast (coefficient4 >>! 12l <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 8)
      ((serialized.[ sz 8 ] <: u8) |. (cast (coefficient5 <<! 1l <: i32) <: u8) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 9)
      (cast (coefficient5 >>! 7l <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 9)
      ((serialized.[ sz 9 ] <: u8) |. (cast (coefficient6 <<! 6l <: i32) <: u8) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 10)
      (cast (coefficient6 >>! 2l <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 11)
      (cast (coefficient6 >>! 10l <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 11)
      ((serialized.[ sz 11 ] <: u8) |. (cast (coefficient7 <<! 3l <: i32) <: u8) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 12)
      (cast (coefficient7 >>! 5l <: i32) <: u8)
  in
  serialized

let deserialize
      (serialized: t_Slice u8)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. sz 13 <: bool)
      in
      ()
  in
  let byte0:i32 = cast (serialized.[ sz 0 ] <: u8) <: i32 in
  let byte1:i32 = cast (serialized.[ sz 1 ] <: u8) <: i32 in
  let byte2:i32 = cast (serialized.[ sz 2 ] <: u8) <: i32 in
  let byte3:i32 = cast (serialized.[ sz 3 ] <: u8) <: i32 in
  let byte4:i32 = cast (serialized.[ sz 4 ] <: u8) <: i32 in
  let byte5:i32 = cast (serialized.[ sz 5 ] <: u8) <: i32 in
  let byte6:i32 = cast (serialized.[ sz 6 ] <: u8) <: i32 in
  let byte7:i32 = cast (serialized.[ sz 7 ] <: u8) <: i32 in
  let byte8:i32 = cast (serialized.[ sz 8 ] <: u8) <: i32 in
  let byte9:i32 = cast (serialized.[ sz 9 ] <: u8) <: i32 in
  let byte10:i32 = cast (serialized.[ sz 10 ] <: u8) <: i32 in
  let byte11:i32 = cast (serialized.[ sz 11 ] <: u8) <: i32 in
  let byte12:i32 = cast (serialized.[ sz 12 ] <: u8) <: i32 in
  let coefficient0:i32 = byte0 in
  let coefficient0:i32 = coefficient0 |. (byte1 <<! 8l <: i32) in
  let coefficient0:i32 = coefficient0 &. deserialize__BITS_IN_LOWER_PART_OF_T_MASK in
  let coefficient1:i32 = byte1 >>! 5l in
  let coefficient1:i32 = coefficient1 |. (byte2 <<! 3l <: i32) in
  let coefficient1:i32 = coefficient1 |. (byte3 <<! 11l <: i32) in
  let coefficient1:i32 = coefficient1 &. deserialize__BITS_IN_LOWER_PART_OF_T_MASK in
  let coefficient2:i32 = byte3 >>! 2l in
  let coefficient2:i32 = coefficient2 |. (byte4 <<! 6l <: i32) in
  let coefficient2:i32 = coefficient2 &. deserialize__BITS_IN_LOWER_PART_OF_T_MASK in
  let coefficient3:i32 = byte4 >>! 7l in
  let coefficient3:i32 = coefficient3 |. (byte5 <<! 1l <: i32) in
  let coefficient3:i32 = coefficient3 |. (byte6 <<! 9l <: i32) in
  let coefficient3:i32 = coefficient3 &. deserialize__BITS_IN_LOWER_PART_OF_T_MASK in
  let coefficient4:i32 = byte6 >>! 4l in
  let coefficient4:i32 = coefficient4 |. (byte7 <<! 4l <: i32) in
  let coefficient4:i32 = coefficient4 |. (byte8 <<! 12l <: i32) in
  let coefficient4:i32 = coefficient4 &. deserialize__BITS_IN_LOWER_PART_OF_T_MASK in
  let coefficient5:i32 = byte8 >>! 1l in
  let coefficient5:i32 = coefficient5 |. (byte9 <<! 7l <: i32) in
  let coefficient5:i32 = coefficient5 &. deserialize__BITS_IN_LOWER_PART_OF_T_MASK in
  let coefficient6:i32 = byte9 >>! 6l in
  let coefficient6:i32 = coefficient6 |. (byte10 <<! 2l <: i32) in
  let coefficient6:i32 = coefficient6 |. (byte11 <<! 10l <: i32) in
  let coefficient6:i32 = coefficient6 &. deserialize__BITS_IN_LOWER_PART_OF_T_MASK in
  let coefficient7:i32 = byte11 >>! 3l in
  let coefficient7:i32 = coefficient7 |. (byte12 <<! 5l <: i32) in
  let coefficient7:i32 = coefficient7 &. deserialize__BITS_IN_LOWER_PART_OF_T_MASK in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (sz 0)
        (change_t0_interval coefficient0 <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (sz 1)
        (change_t0_interval coefficient1 <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (sz 2)
        (change_t0_interval coefficient2 <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (sz 3)
        (change_t0_interval coefficient3 <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (sz 4)
        (change_t0_interval coefficient4 <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (sz 5)
        (change_t0_interval coefficient5 <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (sz 6)
        (change_t0_interval coefficient6 <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (sz 7)
        (change_t0_interval coefficient7 <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  simd_unit
