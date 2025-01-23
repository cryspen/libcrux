module Libcrux_ml_dsa.Simd.Portable.Encoding.Commitment
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let serialize
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
     =
  let serialized:t_Slice u8 =
    match cast (Core.Slice.impl__len #u8 serialized <: usize) <: u8 with
    | Rust_primitives.Integers.MkInt 4 ->
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
              let coefficient0:u8 = cast (coefficients.[ mk_usize 0 ] <: i32) <: u8 in
              let coefficient1:u8 = cast (coefficients.[ mk_usize 1 ] <: i32) <: u8 in
              let serialized:t_Slice u8 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
                  i
                  ((coefficient1 <<! mk_i32 4 <: u8) |. coefficient0 <: u8)
              in
              serialized)
      in
      serialized
    | Rust_primitives.Integers.MkInt 6 ->
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
              let coefficient0:u8 = cast (coefficients.[ mk_usize 0 ] <: i32) <: u8 in
              let coefficient1:u8 = cast (coefficients.[ mk_usize 1 ] <: i32) <: u8 in
              let coefficient2:u8 = cast (coefficients.[ mk_usize 2 ] <: i32) <: u8 in
              let coefficient3:u8 = cast (coefficients.[ mk_usize 3 ] <: i32) <: u8 in
              let serialized:t_Slice u8 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
                  (mk_usize 3 *! i <: usize)
                  ((coefficient1 <<! mk_i32 6 <: u8) |. coefficient0 <: u8)
              in
              let serialized:t_Slice u8 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
                  ((mk_usize 3 *! i <: usize) +! mk_usize 1 <: usize)
                  ((coefficient2 <<! mk_i32 4 <: u8) |. (coefficient1 >>! mk_i32 2 <: u8) <: u8)
              in
              let serialized:t_Slice u8 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
                  ((mk_usize 3 *! i <: usize) +! mk_usize 2 <: usize)
                  ((coefficient3 <<! mk_i32 2 <: u8) |. (coefficient2 >>! mk_i32 4 <: u8) <: u8)
              in
              serialized)
      in
      serialized
    | _ -> serialized
  in
  serialized
