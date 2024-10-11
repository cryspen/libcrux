module Libcrux_ml_dsa.Simd.Portable.Encoding.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Portable in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let deserialize_when_eta_is_2___ETA: i32 = Rust_primitives.mk_i32 2

let deserialize_when_eta_is_4___ETA: i32 = Rust_primitives.mk_i32 4

let serialize_when_eta_is_2___ETA: i32 = Rust_primitives.mk_i32 2

let serialize_when_eta_is_4___ETA: i32 = Rust_primitives.mk_i32 4

let serialize_when_eta_is_2_
      (v_OUTPUT_SIZE: usize)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
    : t_Array u8 v_OUTPUT_SIZE =
  let serialized:t_Array u8 v_OUTPUT_SIZE =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) v_OUTPUT_SIZE
  in
  let coefficient0:u8 =
    cast (serialize_when_eta_is_2___ETA -!
        (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 0 ] <: i32
        )
        <:
        i32)
    <:
    u8
  in
  let coefficient1:u8 =
    cast (serialize_when_eta_is_2___ETA -!
        (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 1 ] <: i32
        )
        <:
        i32)
    <:
    u8
  in
  let coefficient2:u8 =
    cast (serialize_when_eta_is_2___ETA -!
        (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 2 ] <: i32
        )
        <:
        i32)
    <:
    u8
  in
  let coefficient3:u8 =
    cast (serialize_when_eta_is_2___ETA -!
        (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 3 ] <: i32
        )
        <:
        i32)
    <:
    u8
  in
  let coefficient4:u8 =
    cast (serialize_when_eta_is_2___ETA -!
        (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 4 ] <: i32
        )
        <:
        i32)
    <:
    u8
  in
  let coefficient5:u8 =
    cast (serialize_when_eta_is_2___ETA -!
        (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 5 ] <: i32
        )
        <:
        i32)
    <:
    u8
  in
  let coefficient6:u8 =
    cast (serialize_when_eta_is_2___ETA -!
        (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 6 ] <: i32
        )
        <:
        i32)
    <:
    u8
  in
  let coefficient7:u8 =
    cast (serialize_when_eta_is_2___ETA -!
        (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 7 ] <: i32
        )
        <:
        i32)
    <:
    u8
  in
  let serialized:t_Array u8 v_OUTPUT_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 0)
      (((coefficient2 <<! Rust_primitives.mk_i32 6 <: u8) |.
          (coefficient1 <<! Rust_primitives.mk_i32 3 <: u8)
          <:
          u8) |.
        coefficient0
        <:
        u8)
  in
  let serialized:t_Array u8 v_OUTPUT_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 1)
      ((((coefficient5 <<! Rust_primitives.mk_i32 7 <: u8) |.
            (coefficient4 <<! Rust_primitives.mk_i32 4 <: u8)
            <:
            u8) |.
          (coefficient3 <<! Rust_primitives.mk_i32 1 <: u8)
          <:
          u8) |.
        (coefficient2 >>! Rust_primitives.mk_i32 2 <: u8)
        <:
        u8)
  in
  let serialized:t_Array u8 v_OUTPUT_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 2)
      (((coefficient7 <<! Rust_primitives.mk_i32 5 <: u8) |.
          (coefficient6 <<! Rust_primitives.mk_i32 2 <: u8)
          <:
          u8) |.
        (coefficient5 >>! Rust_primitives.mk_i32 1 <: u8)
        <:
        u8)
  in
  serialized

let serialize_when_eta_is_4_
      (v_OUTPUT_SIZE: usize)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
    : t_Array u8 v_OUTPUT_SIZE =
  let serialized:t_Array u8 v_OUTPUT_SIZE =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) v_OUTPUT_SIZE
  in
  let serialized:t_Array u8 v_OUTPUT_SIZE =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (Rust_primitives.mk_usize 2)
      (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients <: t_Slice i32)
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUTPUT_SIZE = serialized in
          let _:usize = temp_1_ in
          true)
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUTPUT_SIZE = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let coefficient0:u8 =
            cast (serialize_when_eta_is_4___ETA -!
                (coefficients.[ Rust_primitives.mk_usize 0 ] <: i32)
                <:
                i32)
            <:
            u8
          in
          let coefficient1:u8 =
            cast (serialize_when_eta_is_4___ETA -!
                (coefficients.[ Rust_primitives.mk_usize 1 ] <: i32)
                <:
                i32)
            <:
            u8
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              i
              ((coefficient1 <<! Rust_primitives.mk_i32 4 <: u8) |. coefficient0 <: u8)
          in
          serialized)
  in
  serialized

let serialize (v_OUTPUT_SIZE: usize) (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
    : t_Array u8 v_OUTPUT_SIZE =
  match cast (v_OUTPUT_SIZE <: usize) <: u8 with
  | 3 -> serialize_when_eta_is_2_ v_OUTPUT_SIZE simd_unit
  | 4 -> serialize_when_eta_is_4_ v_OUTPUT_SIZE simd_unit
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let deserialize_when_eta_is_2_ (serialized: t_Slice u8)
    : Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =.
            Rust_primitives.mk_usize 3
            <:
            bool)
      in
      ()
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let byte0:i32 = cast (serialized.[ Rust_primitives.mk_usize 0 ] <: u8) <: i32 in
  let byte1:i32 = cast (serialized.[ Rust_primitives.mk_usize 1 ] <: u8) <: i32 in
  let byte2:i32 = cast (serialized.[ Rust_primitives.mk_usize 2 ] <: u8) <: i32 in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (Rust_primitives.mk_usize 0)
        (deserialize_when_eta_is_2___ETA -! (byte0 &. Rust_primitives.mk_i32 7 <: i32) <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (Rust_primitives.mk_usize 1)
        (deserialize_when_eta_is_2___ETA -!
          ((byte0 >>! Rust_primitives.mk_i32 3 <: i32) &. Rust_primitives.mk_i32 7 <: i32)
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (Rust_primitives.mk_usize 2)
        (deserialize_when_eta_is_2___ETA -!
          (((byte0 >>! Rust_primitives.mk_i32 6 <: i32) |.
              (byte1 <<! Rust_primitives.mk_i32 2 <: i32)
              <:
              i32) &.
            Rust_primitives.mk_i32 7
            <:
            i32)
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (Rust_primitives.mk_usize 3)
        (deserialize_when_eta_is_2___ETA -!
          ((byte1 >>! Rust_primitives.mk_i32 1 <: i32) &. Rust_primitives.mk_i32 7 <: i32)
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (Rust_primitives.mk_usize 4)
        (deserialize_when_eta_is_2___ETA -!
          ((byte1 >>! Rust_primitives.mk_i32 4 <: i32) &. Rust_primitives.mk_i32 7 <: i32)
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (Rust_primitives.mk_usize 5)
        (deserialize_when_eta_is_2___ETA -!
          (((byte1 >>! Rust_primitives.mk_i32 7 <: i32) |.
              (byte2 <<! Rust_primitives.mk_i32 1 <: i32)
              <:
              i32) &.
            Rust_primitives.mk_i32 7
            <:
            i32)
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (Rust_primitives.mk_usize 6)
        (deserialize_when_eta_is_2___ETA -!
          ((byte2 >>! Rust_primitives.mk_i32 2 <: i32) &. Rust_primitives.mk_i32 7 <: i32)
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (Rust_primitives.mk_usize 7)
        (deserialize_when_eta_is_2___ETA -!
          ((byte2 >>! Rust_primitives.mk_i32 5 <: i32) &. Rust_primitives.mk_i32 7 <: i32)
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  simd_unit

let deserialize_when_eta_is_4_ (serialized: t_Slice u8)
    : Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =.
            Rust_primitives.mk_usize 4
            <:
            bool)
      in
      ()
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    Rust_primitives.Hax.Folds.fold_enumerated_slice serialized
      (fun simd_unit temp_1_ ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit = simd_unit in
          let _:usize = temp_1_ in
          true)
      simd_unit
      (fun simd_unit temp_1_ ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit = simd_unit in
          let i, byte:(usize & u8) = temp_1_ in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                (Rust_primitives.mk_usize 2 *! i <: usize)
                (deserialize_when_eta_is_4___ETA -!
                  (cast (byte &. Rust_primitives.mk_u8 15 <: u8) <: i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                ((Rust_primitives.mk_usize 2 *! i <: usize) +! Rust_primitives.mk_usize 1 <: usize)
                (deserialize_when_eta_is_4___ETA -!
                  (cast (byte >>! Rust_primitives.mk_i32 4 <: u8) <: i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          simd_unit)
  in
  simd_unit

let deserialize (v_ETA: usize) (serialized: t_Slice u8)
    : Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
  match cast (v_ETA <: usize) <: u8 with
  | 2 -> deserialize_when_eta_is_2_ serialized
  | 4 -> deserialize_when_eta_is_4_ serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)
