module Libcrux_ml_dsa.Simd.Portable.Encoding.T0
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Portable in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let change_t0_interval (t0: i32) =
  (Rust_primitives.mk_i32 1 <<!
    (Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T -! Rust_primitives.mk_usize 1 <: usize)
    <:
    i32) -!
  t0

let serialize (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit) =
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) (Rust_primitives.mk_usize 13)
  in
  let coefficient0:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
          0 ]
        <:
        i32)
  in
  let coefficient1:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
          1 ]
        <:
        i32)
  in
  let coefficient2:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
          2 ]
        <:
        i32)
  in
  let coefficient3:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
          3 ]
        <:
        i32)
  in
  let coefficient4:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
          4 ]
        <:
        i32)
  in
  let coefficient5:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
          5 ]
        <:
        i32)
  in
  let coefficient6:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
          6 ]
        <:
        i32)
  in
  let coefficient7:i32 =
    change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
          7 ]
        <:
        i32)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 0)
      (cast (coefficient0 <: i32) <: u8)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 1)
      (cast (coefficient0 >>! Rust_primitives.mk_i32 8 <: i32) <: u8)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 1)
      ((serialized.[ Rust_primitives.mk_usize 1 ] <: u8) |.
        (cast (coefficient1 <<! Rust_primitives.mk_i32 5 <: i32) <: u8)
        <:
        u8)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 2)
      (cast (coefficient1 >>! Rust_primitives.mk_i32 3 <: i32) <: u8)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 3)
      (cast (coefficient1 >>! Rust_primitives.mk_i32 11 <: i32) <: u8)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 3)
      ((serialized.[ Rust_primitives.mk_usize 3 ] <: u8) |.
        (cast (coefficient2 <<! Rust_primitives.mk_i32 2 <: i32) <: u8)
        <:
        u8)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 4)
      (cast (coefficient2 >>! Rust_primitives.mk_i32 6 <: i32) <: u8)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 4)
      ((serialized.[ Rust_primitives.mk_usize 4 ] <: u8) |.
        (cast (coefficient3 <<! Rust_primitives.mk_i32 7 <: i32) <: u8)
        <:
        u8)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 5)
      (cast (coefficient3 >>! Rust_primitives.mk_i32 1 <: i32) <: u8)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 6)
      (cast (coefficient3 >>! Rust_primitives.mk_i32 9 <: i32) <: u8)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 6)
      ((serialized.[ Rust_primitives.mk_usize 6 ] <: u8) |.
        (cast (coefficient4 <<! Rust_primitives.mk_i32 4 <: i32) <: u8)
        <:
        u8)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 7)
      (cast (coefficient4 >>! Rust_primitives.mk_i32 4 <: i32) <: u8)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 8)
      (cast (coefficient4 >>! Rust_primitives.mk_i32 12 <: i32) <: u8)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 8)
      ((serialized.[ Rust_primitives.mk_usize 8 ] <: u8) |.
        (cast (coefficient5 <<! Rust_primitives.mk_i32 1 <: i32) <: u8)
        <:
        u8)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 9)
      (cast (coefficient5 >>! Rust_primitives.mk_i32 7 <: i32) <: u8)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 9)
      ((serialized.[ Rust_primitives.mk_usize 9 ] <: u8) |.
        (cast (coefficient6 <<! Rust_primitives.mk_i32 6 <: i32) <: u8)
        <:
        u8)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 10)
      (cast (coefficient6 >>! Rust_primitives.mk_i32 2 <: i32) <: u8)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 11)
      (cast (coefficient6 >>! Rust_primitives.mk_i32 10 <: i32) <: u8)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 11)
      ((serialized.[ Rust_primitives.mk_usize 11 ] <: u8) |.
        (cast (coefficient7 <<! Rust_primitives.mk_i32 3 <: i32) <: u8)
        <:
        u8)
  in
  let serialized:t_Array u8 (Rust_primitives.mk_usize 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (Rust_primitives.mk_usize 12)
      (cast (coefficient7 >>! Rust_primitives.mk_i32 5 <: i32) <: u8)
  in
  serialized

let deserialize (serialized: t_Slice u8) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =.
            Rust_primitives.mk_usize 13
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
  let byte0:i32 = cast (serialized.[ Rust_primitives.mk_usize 0 ] <: u8) <: i32 in
  let byte1:i32 = cast (serialized.[ Rust_primitives.mk_usize 1 ] <: u8) <: i32 in
  let byte2:i32 = cast (serialized.[ Rust_primitives.mk_usize 2 ] <: u8) <: i32 in
  let byte3:i32 = cast (serialized.[ Rust_primitives.mk_usize 3 ] <: u8) <: i32 in
  let byte4:i32 = cast (serialized.[ Rust_primitives.mk_usize 4 ] <: u8) <: i32 in
  let byte5:i32 = cast (serialized.[ Rust_primitives.mk_usize 5 ] <: u8) <: i32 in
  let byte6:i32 = cast (serialized.[ Rust_primitives.mk_usize 6 ] <: u8) <: i32 in
  let byte7:i32 = cast (serialized.[ Rust_primitives.mk_usize 7 ] <: u8) <: i32 in
  let byte8:i32 = cast (serialized.[ Rust_primitives.mk_usize 8 ] <: u8) <: i32 in
  let byte9:i32 = cast (serialized.[ Rust_primitives.mk_usize 9 ] <: u8) <: i32 in
  let byte10:i32 = cast (serialized.[ Rust_primitives.mk_usize 10 ] <: u8) <: i32 in
  let byte11:i32 = cast (serialized.[ Rust_primitives.mk_usize 11 ] <: u8) <: i32 in
  let byte12:i32 = cast (serialized.[ Rust_primitives.mk_usize 12 ] <: u8) <: i32 in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (Rust_primitives.mk_usize 0)
        byte0
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
        (Rust_primitives.mk_usize 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
              0 ]
            <:
            i32) |.
          (byte1 <<! Rust_primitives.mk_i32 8 <: i32)
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
        (Rust_primitives.mk_usize 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
              0 ]
            <:
            i32) &.
          deserialize__BITS_IN_LOWER_PART_OF_T_MASK
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
        (Rust_primitives.mk_usize 1)
        (byte1 >>! Rust_primitives.mk_i32 5 <: i32)
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
        (Rust_primitives.mk_usize 1)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
              1 ]
            <:
            i32) |.
          (byte2 <<! Rust_primitives.mk_i32 3 <: i32)
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
        (Rust_primitives.mk_usize 1)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
              1 ]
            <:
            i32) |.
          (byte3 <<! Rust_primitives.mk_i32 11 <: i32)
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
        (Rust_primitives.mk_usize 1)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
              1 ]
            <:
            i32) &.
          deserialize__BITS_IN_LOWER_PART_OF_T_MASK
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
        (Rust_primitives.mk_usize 2)
        (byte3 >>! Rust_primitives.mk_i32 2 <: i32)
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
        (Rust_primitives.mk_usize 2)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
              2 ]
            <:
            i32) |.
          (byte4 <<! Rust_primitives.mk_i32 6 <: i32)
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
        (Rust_primitives.mk_usize 2)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
              2 ]
            <:
            i32) &.
          deserialize__BITS_IN_LOWER_PART_OF_T_MASK
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
        (Rust_primitives.mk_usize 3)
        (byte4 >>! Rust_primitives.mk_i32 7 <: i32)
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
        (Rust_primitives.mk_usize 3)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
              3 ]
            <:
            i32) |.
          (byte5 <<! Rust_primitives.mk_i32 1 <: i32)
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
        (Rust_primitives.mk_usize 3)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
              3 ]
            <:
            i32) |.
          (byte6 <<! Rust_primitives.mk_i32 9 <: i32)
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
        (Rust_primitives.mk_usize 3)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
              3 ]
            <:
            i32) &.
          deserialize__BITS_IN_LOWER_PART_OF_T_MASK
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
        (Rust_primitives.mk_usize 4)
        (byte6 >>! Rust_primitives.mk_i32 4 <: i32)
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
        (Rust_primitives.mk_usize 4)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
              4 ]
            <:
            i32) |.
          (byte7 <<! Rust_primitives.mk_i32 4 <: i32)
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
        (Rust_primitives.mk_usize 4)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
              4 ]
            <:
            i32) |.
          (byte8 <<! Rust_primitives.mk_i32 12 <: i32)
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
        (Rust_primitives.mk_usize 4)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
              4 ]
            <:
            i32) &.
          deserialize__BITS_IN_LOWER_PART_OF_T_MASK
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
        (Rust_primitives.mk_usize 5)
        (byte8 >>! Rust_primitives.mk_i32 1 <: i32)
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
        (Rust_primitives.mk_usize 5)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
              5 ]
            <:
            i32) |.
          (byte9 <<! Rust_primitives.mk_i32 7 <: i32)
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
        (Rust_primitives.mk_usize 5)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
              5 ]
            <:
            i32) &.
          deserialize__BITS_IN_LOWER_PART_OF_T_MASK
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
        (Rust_primitives.mk_usize 6)
        (byte9 >>! Rust_primitives.mk_i32 6 <: i32)
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
        (Rust_primitives.mk_usize 6)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
              6 ]
            <:
            i32) |.
          (byte10 <<! Rust_primitives.mk_i32 2 <: i32)
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
        (Rust_primitives.mk_usize 6)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
              6 ]
            <:
            i32) |.
          (byte11 <<! Rust_primitives.mk_i32 10 <: i32)
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
        (Rust_primitives.mk_usize 6)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
              6 ]
            <:
            i32) &.
          deserialize__BITS_IN_LOWER_PART_OF_T_MASK
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
        (Rust_primitives.mk_usize 7)
        (byte11 >>! Rust_primitives.mk_i32 3 <: i32)
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
        (Rust_primitives.mk_usize 7)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
              7 ]
            <:
            i32) |.
          (byte12 <<! Rust_primitives.mk_i32 5 <: i32)
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
        (Rust_primitives.mk_usize 7)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
              7 ]
            <:
            i32) &.
          deserialize__BITS_IN_LOWER_PART_OF_T_MASK
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
        (Rust_primitives.mk_usize 0)
        (change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
                0 ]
              <:
              i32)
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
        (Rust_primitives.mk_usize 1)
        (change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
                1 ]
              <:
              i32)
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
        (Rust_primitives.mk_usize 2)
        (change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
                2 ]
              <:
              i32)
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
        (Rust_primitives.mk_usize 3)
        (change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
                3 ]
              <:
              i32)
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
        (Rust_primitives.mk_usize 4)
        (change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
                4 ]
              <:
              i32)
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
        (Rust_primitives.mk_usize 5)
        (change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
                5 ]
              <:
              i32)
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
        (Rust_primitives.mk_usize 6)
        (change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
                6 ]
              <:
              i32)
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
        (Rust_primitives.mk_usize 7)
        (change_t0_interval (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ Rust_primitives.mk_usize
                7 ]
              <:
              i32)
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  simd_unit
