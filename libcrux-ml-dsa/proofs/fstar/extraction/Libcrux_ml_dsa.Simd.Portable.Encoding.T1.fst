module Libcrux_ml_dsa.Simd.Portable.Encoding.T1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Portable in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let serialize (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit) =
  let serialized:t_Array u8 (Rust_primitives.mk_usize 10) =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) (Rust_primitives.mk_usize 10)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 10) =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (Rust_primitives.mk_usize 4)
      (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients <: t_Slice i32)
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 (Rust_primitives.mk_usize 10) = serialized in
          let _:usize = temp_1_ in
          true)
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 (Rust_primitives.mk_usize 10) = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let serialized:t_Array u8 (Rust_primitives.mk_usize 10) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (Rust_primitives.mk_usize 5 *! i <: usize)
              (cast ((coefficients.[ Rust_primitives.mk_usize 0 ] <: i32) &.
                    Rust_primitives.mk_i32 255
                    <:
                    i32)
                <:
                u8)
          in
          let serialized:t_Array u8 (Rust_primitives.mk_usize 10) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((Rust_primitives.mk_usize 5 *! i <: usize) +! Rust_primitives.mk_usize 1 <: usize)
              (((cast ((coefficients.[ Rust_primitives.mk_usize 1 ] <: i32) &.
                        Rust_primitives.mk_i32 63
                        <:
                        i32)
                    <:
                    u8) <<!
                  Rust_primitives.mk_i32 2
                  <:
                  u8) |.
                (cast (((coefficients.[ Rust_primitives.mk_usize 0 ] <: i32) >>!
                        Rust_primitives.mk_i32 8
                        <:
                        i32) &.
                      Rust_primitives.mk_i32 3
                      <:
                      i32)
                  <:
                  u8)
                <:
                u8)
          in
          let serialized:t_Array u8 (Rust_primitives.mk_usize 10) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((Rust_primitives.mk_usize 5 *! i <: usize) +! Rust_primitives.mk_usize 2 <: usize)
              (((cast ((coefficients.[ Rust_primitives.mk_usize 2 ] <: i32) &.
                        Rust_primitives.mk_i32 15
                        <:
                        i32)
                    <:
                    u8) <<!
                  Rust_primitives.mk_i32 4
                  <:
                  u8) |.
                (cast (((coefficients.[ Rust_primitives.mk_usize 1 ] <: i32) >>!
                        Rust_primitives.mk_i32 6
                        <:
                        i32) &.
                      Rust_primitives.mk_i32 15
                      <:
                      i32)
                  <:
                  u8)
                <:
                u8)
          in
          let serialized:t_Array u8 (Rust_primitives.mk_usize 10) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((Rust_primitives.mk_usize 5 *! i <: usize) +! Rust_primitives.mk_usize 3 <: usize)
              (((cast ((coefficients.[ Rust_primitives.mk_usize 3 ] <: i32) &.
                        Rust_primitives.mk_i32 3
                        <:
                        i32)
                    <:
                    u8) <<!
                  Rust_primitives.mk_i32 6
                  <:
                  u8) |.
                (cast (((coefficients.[ Rust_primitives.mk_usize 2 ] <: i32) >>!
                        Rust_primitives.mk_i32 4
                        <:
                        i32) &.
                      Rust_primitives.mk_i32 63
                      <:
                      i32)
                  <:
                  u8)
                <:
                u8)
          in
          let serialized:t_Array u8 (Rust_primitives.mk_usize 10) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((Rust_primitives.mk_usize 5 *! i <: usize) +! Rust_primitives.mk_usize 4 <: usize)
              (cast (((coefficients.[ Rust_primitives.mk_usize 3 ] <: i32) >>!
                      Rust_primitives.mk_i32 2
                      <:
                      i32) &.
                    Rust_primitives.mk_i32 255
                    <:
                    i32)
                <:
                u8)
          in
          serialized)
  in
  serialized

let deserialize (serialized: t_Slice u8) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =.
            Rust_primitives.mk_usize 10
            <:
            bool)
      in
      ()
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let mask:i32 =
    (Rust_primitives.mk_i32 1 <<! Libcrux_ml_dsa.Constants.v_BITS_IN_UPPER_PART_OF_T <: i32) -!
    Rust_primitives.mk_i32 1
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (Rust_primitives.mk_usize 5)
      serialized
      (fun simd_unit temp_1_ ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit = simd_unit in
          let _:usize = temp_1_ in
          true)
      simd_unit
      (fun simd_unit temp_1_ ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit = simd_unit in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let byte0:i32 = cast (bytes.[ Rust_primitives.mk_usize 0 ] <: u8) <: i32 in
          let byte1:i32 = cast (bytes.[ Rust_primitives.mk_usize 1 ] <: u8) <: i32 in
          let byte2:i32 = cast (bytes.[ Rust_primitives.mk_usize 2 ] <: u8) <: i32 in
          let byte3:i32 = cast (bytes.[ Rust_primitives.mk_usize 3 ] <: u8) <: i32 in
          let byte4:i32 = cast (bytes.[ Rust_primitives.mk_usize 4 ] <: u8) <: i32 in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
                (Rust_primitives.mk_usize 4 *! i <: usize)
                ((byte0 |. (byte1 <<! Rust_primitives.mk_i32 8 <: i32) <: i32) &. mask <: i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
                ((Rust_primitives.mk_usize 4 *! i <: usize) +! Rust_primitives.mk_usize 1 <: usize)
                (((byte1 >>! Rust_primitives.mk_i32 2 <: i32) |.
                    (byte2 <<! Rust_primitives.mk_i32 6 <: i32)
                    <:
                    i32) &.
                  mask
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
                ((Rust_primitives.mk_usize 4 *! i <: usize) +! Rust_primitives.mk_usize 2 <: usize)
                (((byte2 >>! Rust_primitives.mk_i32 4 <: i32) |.
                    (byte3 <<! Rust_primitives.mk_i32 4 <: i32)
                    <:
                    i32) &.
                  mask
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
                ((Rust_primitives.mk_usize 4 *! i <: usize) +! Rust_primitives.mk_usize 3 <: usize)
                (((byte3 >>! Rust_primitives.mk_i32 6 <: i32) |.
                    (byte4 <<! Rust_primitives.mk_i32 2 <: i32)
                    <:
                    i32) &.
                  mask
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
          in
          simd_unit)
  in
  simd_unit
