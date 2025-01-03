module Libcrux_ml_dsa.Simd.Portable.Encoding.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let deserialize_when_eta_is_2_ (serialized: t_Slice u8) (simd_unit: t_Array i32 (sz 8)) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. sz 3 <: bool)
      in
      ()
  in
  let byte0:i32 = cast (serialized.[ sz 0 ] <: u8) <: i32 in
  let byte1:i32 = cast (serialized.[ sz 1 ] <: u8) <: i32 in
  let byte2:i32 = cast (serialized.[ sz 2 ] <: u8) <: i32 in
  let simd_unit:t_Array i32 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
      (sz 0)
      (deserialize_when_eta_is_2___ETA -! (byte0 &. 7l <: i32) <: i32)
  in
  let simd_unit:t_Array i32 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
      (sz 1)
      (deserialize_when_eta_is_2___ETA -! ((byte0 >>! 3l <: i32) &. 7l <: i32) <: i32)
  in
  let simd_unit:t_Array i32 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
      (sz 2)
      (deserialize_when_eta_is_2___ETA -!
        (((byte0 >>! 6l <: i32) |. (byte1 <<! 2l <: i32) <: i32) &. 7l <: i32)
        <:
        i32)
  in
  let simd_unit:t_Array i32 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
      (sz 3)
      (deserialize_when_eta_is_2___ETA -! ((byte1 >>! 1l <: i32) &. 7l <: i32) <: i32)
  in
  let simd_unit:t_Array i32 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
      (sz 4)
      (deserialize_when_eta_is_2___ETA -! ((byte1 >>! 4l <: i32) &. 7l <: i32) <: i32)
  in
  let simd_unit:t_Array i32 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
      (sz 5)
      (deserialize_when_eta_is_2___ETA -!
        (((byte1 >>! 7l <: i32) |. (byte2 <<! 1l <: i32) <: i32) &. 7l <: i32)
        <:
        i32)
  in
  let simd_unit:t_Array i32 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
      (sz 6)
      (deserialize_when_eta_is_2___ETA -! ((byte2 >>! 2l <: i32) &. 7l <: i32) <: i32)
  in
  let simd_unit:t_Array i32 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
      (sz 7)
      (deserialize_when_eta_is_2___ETA -! ((byte2 >>! 5l <: i32) &. 7l <: i32) <: i32)
  in
  simd_unit

let deserialize_when_eta_is_4_ (serialized: t_Slice u8) (simd_units: t_Array i32 (sz 8)) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. sz 4 <: bool)
      in
      ()
  in
  let simd_units:t_Array i32 (sz 8) =
    Rust_primitives.Hax.Folds.fold_enumerated_slice serialized
      (fun simd_units temp_1_ ->
          let simd_units:t_Array i32 (sz 8) = simd_units in
          let _:usize = temp_1_ in
          true)
      simd_units
      (fun simd_units temp_1_ ->
          let simd_units:t_Array i32 (sz 8) = simd_units in
          let i, byte:(usize & u8) = temp_1_ in
          let simd_units:t_Array i32 (sz 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_units
              (sz 2 *! i <: usize)
              (deserialize_when_eta_is_4___ETA -! (cast (byte &. 15uy <: u8) <: i32) <: i32)
          in
          let simd_units:t_Array i32 (sz 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_units
              ((sz 2 *! i <: usize) +! sz 1 <: usize)
              (deserialize_when_eta_is_4___ETA -! (cast (byte >>! 4l <: u8) <: i32) <: i32)
          in
          simd_units)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  simd_units

let deserialize
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (serialized: t_Slice u8)
      (out: t_Array i32 (sz 8))
     =
  let out, hax_temp_output:(t_Array i32 (sz 8) & Prims.unit) =
    match eta <: Libcrux_ml_dsa.Constants.t_Eta with
    | Libcrux_ml_dsa.Constants.Eta_Two  ->
      deserialize_when_eta_is_2_ serialized out, () <: (t_Array i32 (sz 8) & Prims.unit)
    | Libcrux_ml_dsa.Constants.Eta_Four  ->
      deserialize_when_eta_is_4_ serialized out, () <: (t_Array i32 (sz 8) & Prims.unit)
  in
  out

let serialize_when_eta_is_2_ (simd_unit: t_Array i32 (sz 8)) (serialized: t_Slice u8) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. sz 3 <: bool)
      in
      ()
  in
  let coefficient0:u8 =
    cast (serialize_when_eta_is_2___ETA -! (simd_unit.[ sz 0 ] <: i32) <: i32) <: u8
  in
  let coefficient1:u8 =
    cast (serialize_when_eta_is_2___ETA -! (simd_unit.[ sz 1 ] <: i32) <: i32) <: u8
  in
  let coefficient2:u8 =
    cast (serialize_when_eta_is_2___ETA -! (simd_unit.[ sz 2 ] <: i32) <: i32) <: u8
  in
  let coefficient3:u8 =
    cast (serialize_when_eta_is_2___ETA -! (simd_unit.[ sz 3 ] <: i32) <: i32) <: u8
  in
  let coefficient4:u8 =
    cast (serialize_when_eta_is_2___ETA -! (simd_unit.[ sz 4 ] <: i32) <: i32) <: u8
  in
  let coefficient5:u8 =
    cast (serialize_when_eta_is_2___ETA -! (simd_unit.[ sz 5 ] <: i32) <: i32) <: u8
  in
  let coefficient6:u8 =
    cast (serialize_when_eta_is_2___ETA -! (simd_unit.[ sz 6 ] <: i32) <: i32) <: u8
  in
  let coefficient7:u8 =
    cast (serialize_when_eta_is_2___ETA -! (simd_unit.[ sz 7 ] <: i32) <: i32) <: u8
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 0)
      (((coefficient2 <<! 6l <: u8) |. (coefficient1 <<! 3l <: u8) <: u8) |. coefficient0 <: u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 1)
      ((((coefficient5 <<! 7l <: u8) |. (coefficient4 <<! 4l <: u8) <: u8) |.
          (coefficient3 <<! 1l <: u8)
          <:
          u8) |.
        (coefficient2 >>! 2l <: u8)
        <:
        u8)
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 2)
      (((coefficient7 <<! 5l <: u8) |. (coefficient6 <<! 2l <: u8) <: u8) |.
        (coefficient5 >>! 1l <: u8)
        <:
        u8)
  in
  serialized

let serialize_when_eta_is_4_ (simd_unit: t_Array i32 (sz 8)) (serialized: t_Slice u8) =
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 2)
      (simd_unit <: t_Slice i32)
      (fun serialized temp_1_ ->
          let serialized:t_Slice u8 = serialized in
          let _:usize = temp_1_ in
          true)
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Slice u8 = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let coefficient0:u8 =
            cast (serialize_when_eta_is_4___ETA -! (coefficients.[ sz 0 ] <: i32) <: i32) <: u8
          in
          let coefficient1:u8 =
            cast (serialize_when_eta_is_4___ETA -! (coefficients.[ sz 1 ] <: i32) <: i32) <: u8
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              i
              ((coefficient1 <<! 4l <: u8) |. coefficient0 <: u8)
          in
          serialized)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  serialized

let serialize
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (simd_unit: t_Array i32 (sz 8))
      (serialized: t_Slice u8)
     =
  let serialized, hax_temp_output:(t_Slice u8 & Prims.unit) =
    match eta <: Libcrux_ml_dsa.Constants.t_Eta with
    | Libcrux_ml_dsa.Constants.Eta_Two  ->
      serialize_when_eta_is_2_ simd_unit serialized, () <: (t_Slice u8 & Prims.unit)
    | Libcrux_ml_dsa.Constants.Eta_Four  ->
      serialize_when_eta_is_4_ simd_unit serialized, () <: (t_Slice u8 & Prims.unit)
  in
  serialized
