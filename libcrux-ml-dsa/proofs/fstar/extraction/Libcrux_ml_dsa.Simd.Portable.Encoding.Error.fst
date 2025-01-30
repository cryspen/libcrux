module Libcrux_ml_dsa.Simd.Portable.Encoding.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let serialize_when_eta_is_2_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. mk_usize 3 <: bool)
      in
      ()
  in
  let coefficient0:u8 =
    cast (serialize_when_eta_is_2___ETA -!
        (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 0 ] <: i32)
        <:
        i32)
    <:
    u8
  in
  let coefficient1:u8 =
    cast (serialize_when_eta_is_2___ETA -!
        (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 1 ] <: i32)
        <:
        i32)
    <:
    u8
  in
  let coefficient2:u8 =
    cast (serialize_when_eta_is_2___ETA -!
        (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 2 ] <: i32)
        <:
        i32)
    <:
    u8
  in
  let coefficient3:u8 =
    cast (serialize_when_eta_is_2___ETA -!
        (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 3 ] <: i32)
        <:
        i32)
    <:
    u8
  in
  let coefficient4:u8 =
    cast (serialize_when_eta_is_2___ETA -!
        (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 4 ] <: i32)
        <:
        i32)
    <:
    u8
  in
  let coefficient5:u8 =
    cast (serialize_when_eta_is_2___ETA -!
        (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 5 ] <: i32)
        <:
        i32)
    <:
    u8
  in
  let coefficient6:u8 =
    cast (serialize_when_eta_is_2___ETA -!
        (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 6 ] <: i32)
        <:
        i32)
    <:
    u8
  in
  let coefficient7:u8 =
    cast (serialize_when_eta_is_2___ETA -!
        (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 7 ] <: i32)
        <:
        i32)
    <:
    u8
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 0)
      (((coefficient2 <<! mk_i32 6 <: u8) |. (coefficient1 <<! mk_i32 3 <: u8) <: u8) |.
        coefficient0
        <:
        u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 1)
      ((((coefficient5 <<! mk_i32 7 <: u8) |. (coefficient4 <<! mk_i32 4 <: u8) <: u8) |.
          (coefficient3 <<! mk_i32 1 <: u8)
          <:
          u8) |.
        (coefficient2 >>! mk_i32 2 <: u8)
        <:
        u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (mk_usize 2)
      (((coefficient7 <<! mk_i32 5 <: u8) |. (coefficient6 <<! mk_i32 2 <: u8) <: u8) |.
        (coefficient5 >>! mk_i32 1 <: u8)
        <:
        u8)
  in
  serialized

let serialize_when_eta_is_4_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
     =
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (mk_usize 2)
      (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
      (fun serialized temp_1_ ->
          let serialized:t_Slice u8 = serialized in
          let _:usize = temp_1_ in
          true)
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Slice u8 = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let coefficient0:u8 =
            cast (serialize_when_eta_is_4___ETA -! (coefficients.[ mk_usize 0 ] <: i32) <: i32)
            <:
            u8
          in
          let coefficient1:u8 =
            cast (serialize_when_eta_is_4___ETA -! (coefficients.[ mk_usize 1 ] <: i32) <: i32)
            <:
            u8
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              i
              ((coefficient1 <<! mk_i32 4 <: u8) |. coefficient0 <: u8)
          in
          serialized)
  in
  serialized

let serialize
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
     =
  let serialized:t_Slice u8 =
    match eta <: Libcrux_ml_dsa.Constants.t_Eta with
    | Libcrux_ml_dsa.Constants.Eta_Two  -> serialize_when_eta_is_2_ simd_unit serialized
    | Libcrux_ml_dsa.Constants.Eta_Four  -> serialize_when_eta_is_4_ simd_unit serialized
  in
  serialized

let deserialize_when_eta_is_2_
      (serialized: t_Slice u8)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. mk_usize 3 <: bool)
      in
      ()
  in
  let byte0:i32 = cast (serialized.[ mk_usize 0 ] <: u8) <: i32 in
  let byte1:i32 = cast (serialized.[ mk_usize 1 ] <: u8) <: i32 in
  let byte2:i32 = cast (serialized.[ mk_usize 2 ] <: u8) <: i32 in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (mk_usize 0)
        (deserialize_when_eta_is_2___ETA -! (byte0 &. mk_i32 7 <: i32) <: i32)
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
        (deserialize_when_eta_is_2___ETA -! ((byte0 >>! mk_i32 3 <: i32) &. mk_i32 7 <: i32) <: i32)
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
        (deserialize_when_eta_is_2___ETA -!
          (((byte0 >>! mk_i32 6 <: i32) |. (byte1 <<! mk_i32 2 <: i32) <: i32) &. mk_i32 7 <: i32)
          <:
          i32)
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
        (deserialize_when_eta_is_2___ETA -! ((byte1 >>! mk_i32 1 <: i32) &. mk_i32 7 <: i32) <: i32)
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
        (deserialize_when_eta_is_2___ETA -! ((byte1 >>! mk_i32 4 <: i32) &. mk_i32 7 <: i32) <: i32)
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
        (deserialize_when_eta_is_2___ETA -!
          (((byte1 >>! mk_i32 7 <: i32) |. (byte2 <<! mk_i32 1 <: i32) <: i32) &. mk_i32 7 <: i32)
          <:
          i32)
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
        (deserialize_when_eta_is_2___ETA -! ((byte2 >>! mk_i32 2 <: i32) &. mk_i32 7 <: i32) <: i32)
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
        (deserialize_when_eta_is_2___ETA -! ((byte2 >>! mk_i32 5 <: i32) &. mk_i32 7 <: i32) <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  simd_unit

let deserialize_when_eta_is_4_
      (serialized: t_Slice u8)
      (simd_units: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. mk_usize 4 <: bool)
      in
      ()
  in
  let simd_units:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Rust_primitives.Hax.Folds.fold_enumerated_slice serialized
      (fun simd_units temp_1_ ->
          let simd_units:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = simd_units in
          let _:usize = temp_1_ in
          true)
      simd_units
      (fun simd_units temp_1_ ->
          let simd_units:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = simd_units in
          let i, byte:(usize & u8) = temp_1_ in
          let simd_units:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            {
              simd_units with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_units
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                (mk_usize 2 *! i <: usize)
                (deserialize_when_eta_is_4___ETA -! (cast (byte &. mk_u8 15 <: u8) <: i32) <: i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          let simd_units:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            {
              simd_units with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_units
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                ((mk_usize 2 *! i <: usize) +! mk_usize 1 <: usize)
                (deserialize_when_eta_is_4___ETA -! (cast (byte >>! mk_i32 4 <: u8) <: i32) <: i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          simd_units)
  in
  simd_units

let deserialize
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (serialized: t_Slice u8)
      (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
     =
  let out:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    match eta <: Libcrux_ml_dsa.Constants.t_Eta with
    | Libcrux_ml_dsa.Constants.Eta_Two  -> deserialize_when_eta_is_2_ serialized out
    | Libcrux_ml_dsa.Constants.Eta_Four  -> deserialize_when_eta_is_4_ serialized out
  in
  out
