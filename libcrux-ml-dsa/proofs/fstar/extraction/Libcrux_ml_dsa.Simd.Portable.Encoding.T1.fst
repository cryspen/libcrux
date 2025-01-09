module Libcrux_ml_dsa.Simd.Portable.Encoding.T1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let deserialize
      (serialized: t_Slice u8)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. sz 10 <: bool)
      in
      ()
  in
  let mask:i32 = (1l <<! Libcrux_ml_dsa.Constants.v_BITS_IN_UPPER_PART_OF_T <: i32) -! 1l in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 5)
      serialized
      (fun simd_unit temp_1_ ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = simd_unit in
          let _:usize = temp_1_ in
          true)
      simd_unit
      (fun simd_unit temp_1_ ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = simd_unit in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let byte0:i32 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
          let byte1:i32 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
          let byte2:i32 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
          let byte3:i32 = cast (bytes.[ sz 3 ] <: u8) <: i32 in
          let byte4:i32 = cast (bytes.[ sz 4 ] <: u8) <: i32 in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                (sz 4 *! i <: usize)
                ((byte0 |. (byte1 <<! 8l <: i32) <: i32) &. mask <: i32)
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
                ((sz 4 *! i <: usize) +! sz 1 <: usize)
                (((byte1 >>! 2l <: i32) |. (byte2 <<! 6l <: i32) <: i32) &. mask <: i32)
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
                ((sz 4 *! i <: usize) +! sz 2 <: usize)
                (((byte2 >>! 4l <: i32) |. (byte3 <<! 4l <: i32) <: i32) &. mask <: i32)
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
                ((sz 4 *! i <: usize) +! sz 3 <: usize)
                (((byte3 >>! 6l <: i32) |. (byte4 <<! 2l <: i32) <: i32) &. mask <: i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          simd_unit)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  simd_unit

let serialize
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. sz 10 <: bool)
      in
      ()
  in
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 4)
      (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
      (fun serialized temp_1_ ->
          let serialized:t_Slice u8 = serialized in
          let _:usize = temp_1_ in
          true)
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Slice u8 = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (sz 5 *! i <: usize)
              (cast ((coefficients.[ sz 0 ] <: i32) &. 255l <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 1 <: usize)
              (((cast ((coefficients.[ sz 1 ] <: i32) &. 63l <: i32) <: u8) <<! 2l <: u8) |.
                (cast (((coefficients.[ sz 0 ] <: i32) >>! 8l <: i32) &. 3l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 2 <: usize)
              (((cast ((coefficients.[ sz 2 ] <: i32) &. 15l <: i32) <: u8) <<! 4l <: u8) |.
                (cast (((coefficients.[ sz 1 ] <: i32) >>! 6l <: i32) &. 15l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 3 <: usize)
              (((cast ((coefficients.[ sz 3 ] <: i32) &. 3l <: i32) <: u8) <<! 6l <: u8) |.
                (cast (((coefficients.[ sz 2 ] <: i32) >>! 4l <: i32) &. 63l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 4 <: usize)
              (cast (((coefficients.[ sz 3 ] <: i32) >>! 2l <: i32) &. 255l <: i32) <: u8)
          in
          serialized)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  serialized
