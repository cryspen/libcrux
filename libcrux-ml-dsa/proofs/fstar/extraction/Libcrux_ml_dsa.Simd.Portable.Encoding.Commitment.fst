module Libcrux_ml_dsa.Simd.Portable.Encoding.Commitment
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let serialize
      (v_OUTPUT_SIZE: usize)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
     =
  let serialized:t_Array u8 v_OUTPUT_SIZE = Rust_primitives.Hax.repeat 0uy v_OUTPUT_SIZE in
  match cast (v_OUTPUT_SIZE <: usize) <: u8 with
  | 4uy ->
    let serialized:t_Array u8 v_OUTPUT_SIZE =
      Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 2)
        (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients <: t_Slice i32)
        (fun serialized temp_1_ ->
            let serialized:t_Array u8 v_OUTPUT_SIZE = serialized in
            let _:usize = temp_1_ in
            true)
        serialized
        (fun serialized temp_1_ ->
            let serialized:t_Array u8 v_OUTPUT_SIZE = serialized in
            let i, coefficients:(usize & t_Slice i32) = temp_1_ in
            let coefficient0:u8 = cast (coefficients.[ sz 0 ] <: i32) <: u8 in
            let coefficient1:u8 = cast (coefficients.[ sz 1 ] <: i32) <: u8 in
            let serialized:t_Array u8 v_OUTPUT_SIZE =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
                i
                ((coefficient1 <<! 4l <: u8) |. coefficient0 <: u8)
            in
            serialized)
    in
    serialized
  | 6uy ->
    let serialized:t_Array u8 v_OUTPUT_SIZE =
      Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 4)
        (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients <: t_Slice i32)
        (fun serialized temp_1_ ->
            let serialized:t_Array u8 v_OUTPUT_SIZE = serialized in
            let _:usize = temp_1_ in
            true)
        serialized
        (fun serialized temp_1_ ->
            let serialized:t_Array u8 v_OUTPUT_SIZE = serialized in
            let i, coefficients:(usize & t_Slice i32) = temp_1_ in
            let coefficient0:u8 = cast (coefficients.[ sz 0 ] <: i32) <: u8 in
            let coefficient1:u8 = cast (coefficients.[ sz 1 ] <: i32) <: u8 in
            let coefficient2:u8 = cast (coefficients.[ sz 2 ] <: i32) <: u8 in
            let coefficient3:u8 = cast (coefficients.[ sz 3 ] <: i32) <: u8 in
            let serialized:t_Array u8 v_OUTPUT_SIZE =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
                (sz 3 *! i <: usize)
                ((coefficient1 <<! 6l <: u8) |. coefficient0 <: u8)
            in
            let serialized:t_Array u8 v_OUTPUT_SIZE =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
                ((sz 3 *! i <: usize) +! sz 1 <: usize)
                ((coefficient2 <<! 4l <: u8) |. (coefficient1 >>! 2l <: u8) <: u8)
            in
            let serialized:t_Array u8 v_OUTPUT_SIZE =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
                ((sz 3 *! i <: usize) +! sz 2 <: usize)
                ((coefficient3 <<! 2l <: u8) |. (coefficient2 >>! 4l <: u8) <: u8)
            in
            serialized)
    in
    serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)
