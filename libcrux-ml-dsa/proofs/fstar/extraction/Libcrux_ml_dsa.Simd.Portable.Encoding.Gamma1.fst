module Libcrux_ml_dsa.Simd.Portable.Encoding.Gamma1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let serialize_when_gamma1_is_2_pow_17_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
     =
  let serialized:t_Slice u8 =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (mk_usize 4)
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
            serialize_when_gamma1_is_2_pow_17___GAMMA1 -! (coefficients.[ mk_usize 0 ] <: i32)
          in
          let coefficient1:i32 =
            serialize_when_gamma1_is_2_pow_17___GAMMA1 -! (coefficients.[ mk_usize 1 ] <: i32)
          in
          let coefficient2:i32 =
            serialize_when_gamma1_is_2_pow_17___GAMMA1 -! (coefficients.[ mk_usize 2 ] <: i32)
          in
          let coefficient3:i32 =
            serialize_when_gamma1_is_2_pow_17___GAMMA1 -! (coefficients.[ mk_usize 3 ] <: i32)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (mk_usize 9 *! i <: usize)
              (cast (coefficient0 <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((mk_usize 9 *! i <: usize) +! mk_usize 1 <: usize)
              (cast (coefficient0 >>! mk_i32 8 <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((mk_usize 9 *! i <: usize) +! mk_usize 2 <: usize)
              (cast (coefficient0 >>! mk_i32 16 <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((mk_usize 9 *! i <: usize) +! mk_usize 2 <: usize)
              ((serialized.[ (mk_usize 9 *! i <: usize) +! mk_usize 2 <: usize ] <: u8) |.
                (cast (coefficient1 <<! mk_i32 2 <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((mk_usize 9 *! i <: usize) +! mk_usize 3 <: usize)
              (cast (coefficient1 >>! mk_i32 6 <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((mk_usize 9 *! i <: usize) +! mk_usize 4 <: usize)
              (cast (coefficient1 >>! mk_i32 14 <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((mk_usize 9 *! i <: usize) +! mk_usize 4 <: usize)
              ((serialized.[ (mk_usize 9 *! i <: usize) +! mk_usize 4 <: usize ] <: u8) |.
                (cast (coefficient2 <<! mk_i32 4 <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((mk_usize 9 *! i <: usize) +! mk_usize 5 <: usize)
              (cast (coefficient2 >>! mk_i32 4 <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((mk_usize 9 *! i <: usize) +! mk_usize 6 <: usize)
              (cast (coefficient2 >>! mk_i32 12 <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((mk_usize 9 *! i <: usize) +! mk_usize 6 <: usize)
              ((serialized.[ (mk_usize 9 *! i <: usize) +! mk_usize 6 <: usize ] <: u8) |.
                (cast (coefficient3 <<! mk_i32 6 <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((mk_usize 9 *! i <: usize) +! mk_usize 7 <: usize)
              (cast (coefficient3 >>! mk_i32 2 <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((mk_usize 9 *! i <: usize) +! mk_usize 8 <: usize)
              (cast (coefficient3 >>! mk_i32 10 <: i32) <: u8)
          in
          serialized)
  in
  serialized

let serialize_when_gamma1_is_2_pow_19_
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
          let coefficient0:i32 =
            serialize_when_gamma1_is_2_pow_19___GAMMA1 -! (coefficients.[ mk_usize 0 ] <: i32)
          in
          let coefficient1:i32 =
            serialize_when_gamma1_is_2_pow_19___GAMMA1 -! (coefficients.[ mk_usize 1 ] <: i32)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (mk_usize 5 *! i <: usize)
              (cast (coefficient0 <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((mk_usize 5 *! i <: usize) +! mk_usize 1 <: usize)
              (cast (coefficient0 >>! mk_i32 8 <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((mk_usize 5 *! i <: usize) +! mk_usize 2 <: usize)
              (cast (coefficient0 >>! mk_i32 16 <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((mk_usize 5 *! i <: usize) +! mk_usize 2 <: usize)
              ((serialized.[ (mk_usize 5 *! i <: usize) +! mk_usize 2 <: usize ] <: u8) |.
                (cast (coefficient1 <<! mk_i32 4 <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((mk_usize 5 *! i <: usize) +! mk_usize 3 <: usize)
              (cast (coefficient1 >>! mk_i32 4 <: i32) <: u8)
          in
          let serialized:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((mk_usize 5 *! i <: usize) +! mk_usize 4 <: usize)
              (cast (coefficient1 >>! mk_i32 12 <: i32) <: u8)
          in
          serialized)
  in
  serialized

let serialize
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
      (gamma1_exponent: usize)
     =
  let serialized:t_Slice u8 =
    match cast (gamma1_exponent <: usize) <: u8 with
    | Rust_primitives.Integers.MkInt 17 -> serialize_when_gamma1_is_2_pow_17_ simd_unit serialized
    | Rust_primitives.Integers.MkInt 19 -> serialize_when_gamma1_is_2_pow_19_ simd_unit serialized
    | _ -> serialized
  in
  serialized

let deserialize_when_gamma1_is_2_pow_17_
      (serialized: t_Slice u8)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. mk_usize 18 <: bool)
      in
      ()
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (mk_usize 9)
      serialized
      (fun simd_unit temp_1_ ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = simd_unit in
          let _:usize = temp_1_ in
          true)
      simd_unit
      (fun simd_unit temp_1_ ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = simd_unit in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let coefficient0:i32 = cast (bytes.[ mk_usize 0 ] <: u8) <: i32 in
          let coefficient0:i32 =
            coefficient0 |. ((cast (bytes.[ mk_usize 1 ] <: u8) <: i32) <<! mk_i32 8 <: i32)
          in
          let coefficient0:i32 =
            coefficient0 |. ((cast (bytes.[ mk_usize 2 ] <: u8) <: i32) <<! mk_i32 16 <: i32)
          in
          let coefficient0:i32 =
            coefficient0 &. deserialize_when_gamma1_is_2_pow_17___GAMMA1_TIMES_2_BITMASK
          in
          let coefficient1:i32 = (cast (bytes.[ mk_usize 2 ] <: u8) <: i32) >>! mk_i32 2 in
          let coefficient1:i32 =
            coefficient1 |. ((cast (bytes.[ mk_usize 3 ] <: u8) <: i32) <<! mk_i32 6 <: i32)
          in
          let coefficient1:i32 =
            coefficient1 |. ((cast (bytes.[ mk_usize 4 ] <: u8) <: i32) <<! mk_i32 14 <: i32)
          in
          let coefficient1:i32 =
            coefficient1 &. deserialize_when_gamma1_is_2_pow_17___GAMMA1_TIMES_2_BITMASK
          in
          let coefficient2:i32 = (cast (bytes.[ mk_usize 4 ] <: u8) <: i32) >>! mk_i32 4 in
          let coefficient2:i32 =
            coefficient2 |. ((cast (bytes.[ mk_usize 5 ] <: u8) <: i32) <<! mk_i32 4 <: i32)
          in
          let coefficient2:i32 =
            coefficient2 |. ((cast (bytes.[ mk_usize 6 ] <: u8) <: i32) <<! mk_i32 12 <: i32)
          in
          let coefficient2:i32 =
            coefficient2 &. deserialize_when_gamma1_is_2_pow_17___GAMMA1_TIMES_2_BITMASK
          in
          let coefficient3:i32 = (cast (bytes.[ mk_usize 6 ] <: u8) <: i32) >>! mk_i32 6 in
          let coefficient3:i32 =
            coefficient3 |. ((cast (bytes.[ mk_usize 7 ] <: u8) <: i32) <<! mk_i32 2 <: i32)
          in
          let coefficient3:i32 =
            coefficient3 |. ((cast (bytes.[ mk_usize 8 ] <: u8) <: i32) <<! mk_i32 10 <: i32)
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
                (mk_usize 4 *! i <: usize)
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
                ((mk_usize 4 *! i <: usize) +! mk_usize 1 <: usize)
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
                ((mk_usize 4 *! i <: usize) +! mk_usize 2 <: usize)
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
                ((mk_usize 4 *! i <: usize) +! mk_usize 3 <: usize)
                (deserialize_when_gamma1_is_2_pow_17___GAMMA1 -! coefficient3 <: i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          simd_unit)
  in
  simd_unit

let deserialize_when_gamma1_is_2_pow_19_
      (serialized: t_Slice u8)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. mk_usize 20 <: bool)
      in
      ()
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (mk_usize 5)
      serialized
      (fun simd_unit temp_1_ ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = simd_unit in
          let _:usize = temp_1_ in
          true)
      simd_unit
      (fun simd_unit temp_1_ ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = simd_unit in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let coefficient0:i32 = cast (bytes.[ mk_usize 0 ] <: u8) <: i32 in
          let coefficient0:i32 =
            coefficient0 |. ((cast (bytes.[ mk_usize 1 ] <: u8) <: i32) <<! mk_i32 8 <: i32)
          in
          let coefficient0:i32 =
            coefficient0 |. ((cast (bytes.[ mk_usize 2 ] <: u8) <: i32) <<! mk_i32 16 <: i32)
          in
          let coefficient0:i32 =
            coefficient0 &. deserialize_when_gamma1_is_2_pow_19___GAMMA1_TIMES_2_BITMASK
          in
          let coefficient1:i32 = (cast (bytes.[ mk_usize 2 ] <: u8) <: i32) >>! mk_i32 4 in
          let coefficient1:i32 =
            coefficient1 |. ((cast (bytes.[ mk_usize 3 ] <: u8) <: i32) <<! mk_i32 4 <: i32)
          in
          let coefficient1:i32 =
            coefficient1 |. ((cast (bytes.[ mk_usize 4 ] <: u8) <: i32) <<! mk_i32 12 <: i32)
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                (mk_usize 2 *! i <: usize)
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
                ((mk_usize 2 *! i <: usize) +! mk_usize 1 <: usize)
                (deserialize_when_gamma1_is_2_pow_19___GAMMA1 -! coefficient1 <: i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          simd_unit)
  in
  simd_unit

let deserialize
      (serialized: t_Slice u8)
      (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (gamma1_exponent: usize)
     =
  let out:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    match cast (gamma1_exponent <: usize) <: u8 with
    | Rust_primitives.Integers.MkInt 17 -> deserialize_when_gamma1_is_2_pow_17_ serialized out
    | Rust_primitives.Integers.MkInt 19 -> deserialize_when_gamma1_is_2_pow_19_ serialized out
    | _ -> out
  in
  out
