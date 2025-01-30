module Libcrux_ml_dsa.Simd.Portable.Encoding.T0
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let change_t0_interval (t0: i32) =
  (mk_i32 1 <<! (Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T -! mk_usize 1 <: usize) <: i32) -!
  t0

let serialize
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. mk_usize 13 <: bool)
      in
      ()
  in
  let coefficient0:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 0 ]
        <:
        i32)
  in
  let coefficient1:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 1 ]
        <:
        i32)
  in
  let coefficient2:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 2 ]
        <:
        i32)
  in
  let coefficient3:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 3 ]
        <:
        i32)
  in
  let coefficient4:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 4 ]
        <:
        i32)
  in
  let coefficient5:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 5 ]
        <:
        i32)
  in
  let coefficient6:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 6 ]
        <:
        i32)
  in
  let coefficient7:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 7 ]
        <:
        i32)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 0)
      (cast (coefficient0 <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 1)
      (cast (coefficient0 >>! mk_i32 8 <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 1)
      ((serialized.[ mk_usize 1 ] <: u8) |. (cast (coefficient1 <<! mk_i32 5 <: i32) <: u8) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 2)
      (cast (coefficient1 >>! mk_i32 3 <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 3)
      (cast (coefficient1 >>! mk_i32 11 <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 3)
      ((serialized.[ mk_usize 3 ] <: u8) |. (cast (coefficient2 <<! mk_i32 2 <: i32) <: u8) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 4)
      (cast (coefficient2 >>! mk_i32 6 <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 4)
      ((serialized.[ mk_usize 4 ] <: u8) |. (cast (coefficient3 <<! mk_i32 7 <: i32) <: u8) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 5)
      (cast (coefficient3 >>! mk_i32 1 <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 6)
      (cast (coefficient3 >>! mk_i32 9 <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 6)
      ((serialized.[ mk_usize 6 ] <: u8) |. (cast (coefficient4 <<! mk_i32 4 <: i32) <: u8) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 7)
      (cast (coefficient4 >>! mk_i32 4 <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 8)
      (cast (coefficient4 >>! mk_i32 12 <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 8)
      ((serialized.[ mk_usize 8 ] <: u8) |. (cast (coefficient5 <<! mk_i32 1 <: i32) <: u8) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 9)
      (cast (coefficient5 >>! mk_i32 7 <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 9)
      ((serialized.[ mk_usize 9 ] <: u8) |. (cast (coefficient6 <<! mk_i32 6 <: i32) <: u8) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 10)
      (cast (coefficient6 >>! mk_i32 2 <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 11)
      (cast (coefficient6 >>! mk_i32 10 <: i32) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 11)
      ((serialized.[ mk_usize 11 ] <: u8) |. (cast (coefficient7 <<! mk_i32 3 <: i32) <: u8) <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 12)
      (cast (coefficient7 >>! mk_i32 5 <: i32) <: u8)
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
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. mk_usize 13 <: bool)
      in
      ()
  in
  let byte0:i32 = cast (serialized.[ mk_usize 0 ] <: u8) <: i32 in
  let byte1:i32 = cast (serialized.[ mk_usize 1 ] <: u8) <: i32 in
  let byte2:i32 = cast (serialized.[ mk_usize 2 ] <: u8) <: i32 in
  let byte3:i32 = cast (serialized.[ mk_usize 3 ] <: u8) <: i32 in
  let byte4:i32 = cast (serialized.[ mk_usize 4 ] <: u8) <: i32 in
  let byte5:i32 = cast (serialized.[ mk_usize 5 ] <: u8) <: i32 in
  let byte6:i32 = cast (serialized.[ mk_usize 6 ] <: u8) <: i32 in
  let byte7:i32 = cast (serialized.[ mk_usize 7 ] <: u8) <: i32 in
  let byte8:i32 = cast (serialized.[ mk_usize 8 ] <: u8) <: i32 in
  let byte9:i32 = cast (serialized.[ mk_usize 9 ] <: u8) <: i32 in
  let byte10:i32 = cast (serialized.[ mk_usize 10 ] <: u8) <: i32 in
  let byte11:i32 = cast (serialized.[ mk_usize 11 ] <: u8) <: i32 in
  let byte12:i32 = cast (serialized.[ mk_usize 12 ] <: u8) <: i32 in
  let coefficient0:i32 = byte0 in
  let coefficient0:i32 = coefficient0 |. (byte1 <<! mk_i32 8 <: i32) in
  let coefficient0:i32 = coefficient0 &. deserialize__v_BITS_IN_LOWER_PART_OF_T_MASK in
  let coefficient1:i32 = byte1 >>! mk_i32 5 in
  let coefficient1:i32 = coefficient1 |. (byte2 <<! mk_i32 3 <: i32) in
  let coefficient1:i32 = coefficient1 |. (byte3 <<! mk_i32 11 <: i32) in
  let coefficient1:i32 = coefficient1 &. deserialize__v_BITS_IN_LOWER_PART_OF_T_MASK in
  let coefficient2:i32 = byte3 >>! mk_i32 2 in
  let coefficient2:i32 = coefficient2 |. (byte4 <<! mk_i32 6 <: i32) in
  let coefficient2:i32 = coefficient2 &. deserialize__v_BITS_IN_LOWER_PART_OF_T_MASK in
  let coefficient3:i32 = byte4 >>! mk_i32 7 in
  let coefficient3:i32 = coefficient3 |. (byte5 <<! mk_i32 1 <: i32) in
  let coefficient3:i32 = coefficient3 |. (byte6 <<! mk_i32 9 <: i32) in
  let coefficient3:i32 = coefficient3 &. deserialize__v_BITS_IN_LOWER_PART_OF_T_MASK in
  let coefficient4:i32 = byte6 >>! mk_i32 4 in
  let coefficient4:i32 = coefficient4 |. (byte7 <<! mk_i32 4 <: i32) in
  let coefficient4:i32 = coefficient4 |. (byte8 <<! mk_i32 12 <: i32) in
  let coefficient4:i32 = coefficient4 &. deserialize__v_BITS_IN_LOWER_PART_OF_T_MASK in
  let coefficient5:i32 = byte8 >>! mk_i32 1 in
  let coefficient5:i32 = coefficient5 |. (byte9 <<! mk_i32 7 <: i32) in
  let coefficient5:i32 = coefficient5 &. deserialize__v_BITS_IN_LOWER_PART_OF_T_MASK in
  let coefficient6:i32 = byte9 >>! mk_i32 6 in
  let coefficient6:i32 = coefficient6 |. (byte10 <<! mk_i32 2 <: i32) in
  let coefficient6:i32 = coefficient6 |. (byte11 <<! mk_i32 10 <: i32) in
  let coefficient6:i32 = coefficient6 &. deserialize__v_BITS_IN_LOWER_PART_OF_T_MASK in
  let coefficient7:i32 = byte11 >>! mk_i32 3 in
  let coefficient7:i32 = coefficient7 |. (byte12 <<! mk_i32 5 <: i32) in
  let coefficient7:i32 = coefficient7 &. deserialize__v_BITS_IN_LOWER_PART_OF_T_MASK in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (mk_usize 0)
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
        (mk_usize 1)
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
        (mk_usize 2)
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
        (mk_usize 3)
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
        (mk_usize 4)
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
        (mk_usize 5)
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
        (mk_usize 6)
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
        (mk_usize 7)
        (change_t0_interval coefficient7 <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  simd_unit
