module Libcrux_ml_dsa.Simd.Portable.Encoding.Gamma1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let deserialize_when_gamma1_is_2_pow_17_
      (serialized: t_Slice u8)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. sz 18 <: bool)
      in
      ()
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 9)
      serialized
      (fun simd_unit temp_1_ ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = simd_unit in
          let _:usize = temp_1_ in
          true)
      simd_unit
      (fun simd_unit temp_1_ ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = simd_unit in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let coefficient0:i32 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
          let coefficient0:i32 =
            coefficient0 |. ((cast (bytes.[ sz 1 ] <: u8) <: i32) <<! 8l <: i32)
          in
          let coefficient0:i32 =
            coefficient0 |. ((cast (bytes.[ sz 2 ] <: u8) <: i32) <<! 16l <: i32)
          in
          let coefficient0:i32 =
            coefficient0 &. deserialize_when_gamma1_is_2_pow_17___GAMMA1_TIMES_2_BITMASK
          in
          let coefficient1:i32 = (cast (bytes.[ sz 2 ] <: u8) <: i32) >>! 2l in
          let coefficient1:i32 =
            coefficient1 |. ((cast (bytes.[ sz 3 ] <: u8) <: i32) <<! 6l <: i32)
          in
          let coefficient1:i32 =
            coefficient1 |. ((cast (bytes.[ sz 4 ] <: u8) <: i32) <<! 14l <: i32)
          in
          let coefficient1:i32 =
            coefficient1 &. deserialize_when_gamma1_is_2_pow_17___GAMMA1_TIMES_2_BITMASK
          in
          let coefficient2:i32 = (cast (bytes.[ sz 4 ] <: u8) <: i32) >>! 4l in
          let coefficient2:i32 =
            coefficient2 |. ((cast (bytes.[ sz 5 ] <: u8) <: i32) <<! 4l <: i32)
          in
          let coefficient2:i32 =
            coefficient2 |. ((cast (bytes.[ sz 6 ] <: u8) <: i32) <<! 12l <: i32)
          in
          let coefficient2:i32 =
            coefficient2 &. deserialize_when_gamma1_is_2_pow_17___GAMMA1_TIMES_2_BITMASK
          in
          let coefficient3:i32 = (cast (bytes.[ sz 6 ] <: u8) <: i32) >>! 6l in
          let coefficient3:i32 =
            coefficient3 |. ((cast (bytes.[ sz 7 ] <: u8) <: i32) <<! 2l <: i32)
          in
          let coefficient3:i32 =
            coefficient3 |. ((cast (bytes.[ sz 8 ] <: u8) <: i32) <<! 10l <: i32)
          in
          let coefficient3:i32 =
            coefficient3 &. deserialize_when_gamma1_is_2_pow_17___GAMMA1_TIMES_2_BITMASK
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                (sz 4 *! i <: usize)
                (deserialize_when_gamma1_is_2_pow_17___GAMMA1 -! coefficient0 <: i32)
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
                (deserialize_when_gamma1_is_2_pow_17___GAMMA1 -! coefficient1 <: i32)
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
                (deserialize_when_gamma1_is_2_pow_17___GAMMA1 -! coefficient2 <: i32)
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
                (deserialize_when_gamma1_is_2_pow_17___GAMMA1 -! coefficient3 <: i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          simd_unit)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  simd_unit

let deserialize_when_gamma1_is_2_pow_19_
      (serialized: t_Slice u8)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. sz 20 <: bool)
      in
      ()
  in
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
          let coefficient0:i32 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
          let coefficient0:i32 =
            coefficient0 |. ((cast (bytes.[ sz 1 ] <: u8) <: i32) <<! 8l <: i32)
          in
          let coefficient0:i32 =
            coefficient0 |. ((cast (bytes.[ sz 2 ] <: u8) <: i32) <<! 16l <: i32)
          in
          let coefficient0:i32 =
            coefficient0 &. deserialize_when_gamma1_is_2_pow_19___GAMMA1_TIMES_2_BITMASK
          in
          let coefficient1:i32 = (cast (bytes.[ sz 2 ] <: u8) <: i32) >>! 4l in
          let coefficient1:i32 =
            coefficient1 |. ((cast (bytes.[ sz 3 ] <: u8) <: i32) <<! 4l <: i32)
          in
          let coefficient1:i32 =
            coefficient1 |. ((cast (bytes.[ sz 4 ] <: u8) <: i32) <<! 12l <: i32)
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                (sz 2 *! i <: usize)
                (deserialize_when_gamma1_is_2_pow_19___GAMMA1 -! coefficient0 <: i32)
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
                ((sz 2 *! i <: usize) +! sz 1 <: usize)
                (deserialize_when_gamma1_is_2_pow_19___GAMMA1 -! coefficient1 <: i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          simd_unit)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  simd_unit

let deserialize
      (serialized: t_Slice u8)
      (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (gamma1_exponent: usize)
     =
  let out, hax_temp_output:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & Prims.unit) =
    match cast (gamma1_exponent <: usize) <: u8 with
    | 17uy ->
      deserialize_when_gamma1_is_2_pow_17_ serialized out, ()
      <:
      (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & Prims.unit)
    | 19uy ->
      deserialize_when_gamma1_is_2_pow_19_ serialized out, ()
      <:
      (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & Prims.unit)
    | _ ->
      out,
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

          <:
          Rust_primitives.Hax.t_Never)
      <:
      (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & Prims.unit)
  in
  out

let serialize_when_gamma1_is_2_pow_17_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
     =
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
          let coefficient0:i32 =
            serialize_when_gamma1_is_2_pow_17___GAMMA1 -! (coefficients.[ sz 0 ] <: i32)
          in
          let coefficient1:i32 =
            serialize_when_gamma1_is_2_pow_17___GAMMA1 -! (coefficients.[ sz 1 ] <: i32)
          in
          let coefficient2:i32 =
            serialize_when_gamma1_is_2_pow_17___GAMMA1 -! (coefficients.[ sz 2 ] <: i32)
          in
          let coefficient3:i32 =
            serialize_when_gamma1_is_2_pow_17___GAMMA1 -! (coefficients.[ sz 3 ] <: i32)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (sz 9 *! i <: usize)
              (cast (coefficient0 <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 1 <: usize)
              (cast (coefficient0 >>! 8l <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 2 <: usize)
              (cast (coefficient0 >>! 16l <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 2 <: usize)
              ((serialized.[ (sz 9 *! i <: usize) +! sz 2 <: usize ] <: u8) |.
                (cast (coefficient1 <<! 2l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 3 <: usize)
              (cast (coefficient1 >>! 6l <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 4 <: usize)
              (cast (coefficient1 >>! 14l <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 4 <: usize)
              ((serialized.[ (sz 9 *! i <: usize) +! sz 4 <: usize ] <: u8) |.
                (cast (coefficient2 <<! 4l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 5 <: usize)
              (cast (coefficient2 >>! 4l <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 6 <: usize)
              (cast (coefficient2 >>! 12l <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 6 <: usize)
              ((serialized.[ (sz 9 *! i <: usize) +! sz 6 <: usize ] <: u8) |.
                (cast (coefficient3 <<! 6l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 7 <: usize)
              (cast (coefficient3 >>! 2l <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 8 <: usize)
              (cast (coefficient3 >>! 10l <: i32) <: u8)
          in
          serialized)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  serialized

let serialize_when_gamma1_is_2_pow_19_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
     =
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 2)
      (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
      (fun serialized temp_1_ ->
          let serialized:t_Slice u8 = serialized in
          let _:usize = temp_1_ in
          true)
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Slice u8 = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let coefficient0:i32 =
            serialize_when_gamma1_is_2_pow_19___GAMMA1 -! (coefficients.[ sz 0 ] <: i32)
          in
          let coefficient1:i32 =
            serialize_when_gamma1_is_2_pow_19___GAMMA1 -! (coefficients.[ sz 1 ] <: i32)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (sz 5 *! i <: usize)
              (cast (coefficient0 <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 1 <: usize)
              (cast (coefficient0 >>! 8l <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 2 <: usize)
              (cast (coefficient0 >>! 16l <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 2 <: usize)
              ((serialized.[ (sz 5 *! i <: usize) +! sz 2 <: usize ] <: u8) |.
                (cast (coefficient1 <<! 4l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 3 <: usize)
              (cast (coefficient1 >>! 4l <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 4 <: usize)
              (cast (coefficient1 >>! 12l <: i32) <: u8)
          in
          serialized)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  serialized

let serialize
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
      (gamma1_exponent: usize)
     =
  let serialized, hax_temp_output:(t_Slice u8 & Prims.unit) =
    match cast (gamma1_exponent <: usize) <: u8 with
    | 17uy ->
      serialize_when_gamma1_is_2_pow_17_ simd_unit serialized, () <: (t_Slice u8 & Prims.unit)
    | 19uy ->
      serialize_when_gamma1_is_2_pow_19_ simd_unit serialized, () <: (t_Slice u8 & Prims.unit)
    | _ ->
      serialized,
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

          <:
          Rust_primitives.Hax.t_Never)
      <:
      (t_Slice u8 & Prims.unit)
  in
  serialized
