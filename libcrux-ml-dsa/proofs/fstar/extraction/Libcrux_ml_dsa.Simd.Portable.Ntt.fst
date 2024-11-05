module Libcrux_ml_dsa.Simd.Portable.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let invert_ntt_at_layer_0_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
      (zeta0 zeta1 zeta2 zeta3: i32)
     =
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 1 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 0 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 0 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 1 ] <: i32)
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
        (sz 1)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta0
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 3 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 2 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 2)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 2 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 3 ] <: i32)
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
        (sz 3)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 5 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 4 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 4)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 4 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 5 ] <: i32)
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
        (sz 5)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta2
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 7 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 6 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 6)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 6 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 7 ] <: i32)
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
        (sz 7)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta3
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  simd_unit

let invert_ntt_at_layer_1_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
      (zeta0 zeta1: i32)
     =
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 2 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 0 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 0 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 2 ] <: i32)
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
        (sz 2)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta0
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 3 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 1 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 1)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 1 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 3 ] <: i32)
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
        (sz 3)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta0
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 6 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 4 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 4)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 4 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 6 ] <: i32)
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
        (sz 6)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 7 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 5 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 5)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 5 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 7 ] <: i32)
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
        (sz 7)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  simd_unit

let invert_ntt_at_layer_2_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
      (zeta: i32)
     =
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 4 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 0 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 0 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 4 ] <: i32)
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
        (sz 4)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32
        )
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 5 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 1 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 1)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 1 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 5 ] <: i32)
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
        (sz 5)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32
        )
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 6 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 2 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 2)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 2 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 6 ] <: i32)
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
        (sz 6)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32
        )
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 7 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 3 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 3)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 3 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 7 ] <: i32)
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
        (sz 7)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32
        )
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  simd_unit

let simd_unit_ntt_at_layer_0_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
      (zeta0 zeta1 zeta2 zeta3: i32)
     =
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 1 ]
        <:
        i32)
      zeta0
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 1)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 0 ] <: i32) -! t
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
        (sz 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 0 ] <: i32) +! t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 3 ]
        <:
        i32)
      zeta1
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 3)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 2 ] <: i32) -! t
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
        (sz 2)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 2 ] <: i32) +! t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 5 ]
        <:
        i32)
      zeta2
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 5)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 4 ] <: i32) -! t
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
        (sz 4)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 4 ] <: i32) +! t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 7 ]
        <:
        i32)
      zeta3
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 7)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 6 ] <: i32) -! t
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
        (sz 6)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 6 ] <: i32) +! t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  simd_unit

let ntt_at_layer_0_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 0)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 0 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          2091667l
          3407706l
          2316500l
          3817976l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 1)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 1 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-3342478l)
          2244091l
          (-2446433l)
          (-3562462l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 2)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 2 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          266997l
          2434439l
          (-1235728l)
          3513181l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 3)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 3 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-3520352l)
          (-3759364l)
          (-1197226l)
          (-3193378l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 4)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 4 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          900702l
          1859098l
          909542l
          819034l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 5)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 5 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          495491l
          (-1613174l)
          (-43260l)
          (-522500l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 6)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 6 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-655327l)
          (-3122442l)
          2031748l
          3207046l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 7)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 7 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-3556995l)
          (-525098l)
          (-768622l)
          (-3595838l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 8)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 8 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          342297l
          286988l
          (-2437823l)
          4108315l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 9)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 9 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          3437287l
          (-3342277l)
          1735879l
          203044l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 10)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 10 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          2842341l
          2691481l
          (-2590150l)
          1265009l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 11)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 11 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          4055324l
          1247620l
          2486353l
          1595974l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 12)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 12 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-3767016l)
          1250494l
          2635921l
          (-3548272l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 13)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 13 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-2994039l)
          1869119l
          1903435l
          (-1050970l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 14)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 14 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-1333058l)
          1237275l
          (-3318210l)
          (-1430225l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 15)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 15 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-451100l)
          1312455l
          3306115l
          (-1962642l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 16)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 16 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-1279661l)
          1917081l
          (-2546312l)
          (-1374803l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 17)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 17 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          1500165l
          777191l
          2235880l
          3406031l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 18)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 18 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-542412l)
          (-2831860l)
          (-1671176l)
          (-1846953l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 19)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 19 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-2584293l)
          (-3724270l)
          594136l
          (-3776993l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 20)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 20 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-2013608l)
          2432395l
          2454455l
          (-164721l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 21)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 21 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          1957272l
          3369112l
          185531l
          (-1207385l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 22)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 22 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-3183426l)
          162844l
          1616392l
          3014001l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 23)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 23 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          810149l
          1652634l
          (-3694233l)
          (-1799107l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 24)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 24 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-3038916l)
          3523897l
          3866901l
          269760l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 25)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 25 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          2213111l
          (-975884l)
          1717735l
          472078l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 26)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 26 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-426683l)
          1723600l
          (-1803090l)
          1910376l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 27)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 27 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-1667432l)
          (-1104333l)
          (-260646l)
          (-3833893l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 28)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 28 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-2939036l)
          (-2235985l)
          (-420899l)
          (-2286327l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 29)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 29 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          183443l
          (-976891l)
          1612842l
          (-3545687l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 30)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 30 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-554416l)
          3919660l
          (-48306l)
          (-1362209l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 31)
      (simd_unit_ntt_at_layer_0_ (re.[ sz 31 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          3937738l
          1400424l
          (-846154l)
          1976782l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  re

let simd_unit_ntt_at_layer_1_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
      (zeta1 zeta2: i32)
     =
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 2 ]
        <:
        i32)
      zeta1
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 2)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 0 ] <: i32) -! t
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
        (sz 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 0 ] <: i32) +! t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 3 ]
        <:
        i32)
      zeta1
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 3)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 1 ] <: i32) -! t
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
        (sz 1)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 1 ] <: i32) +! t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 6 ]
        <:
        i32)
      zeta2
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 6)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 4 ] <: i32) -! t
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
        (sz 4)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 4 ] <: i32) +! t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 7 ]
        <:
        i32)
      zeta2
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 7)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 5 ] <: i32) -! t
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
        (sz 5)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 5 ] <: i32) +! t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  simd_unit

let ntt_at_layer_1_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 0)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 0 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-3930395l)
          (-1528703l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 1)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 1 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-3677745l)
          (-3041255l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 2)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 2 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-1452451l)
          3475950l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 3)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 3 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          2176455l
          (-1585221l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 4)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 4 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-1257611l)
          1939314l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 5)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 5 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-4083598l)
          (-1000202l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 6)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 6 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-3190144l)
          (-3157330l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 7)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 7 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-3632928l)
          126922l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 8)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 8 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          3412210l
          (-983419l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 9)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 9 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          2147896l
          2715295l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 10)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 10 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-2967645l)
          (-3693493l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 11)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 11 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-411027l)
          (-2477047l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 12)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 12 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-671102l)
          (-1228525l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 13)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 13 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-22981l)
          (-1308169l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 14)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 14 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-381987l)
          1349076l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 15)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 15 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          1852771l
          (-1430430l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 16)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 16 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-3343383l)
          264944l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 17)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 17 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          508951l
          3097992l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 18)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 18 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          44288l
          (-1100098l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 19)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 19 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          904516l
          3958618l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 20)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 20 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-3724342l)
          (-8578l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 21)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 21 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          1653064l
          (-3249728l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 22)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 22 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          2389356l
          (-210977l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 23)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 23 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          759969l
          (-1316856l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 24)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 24 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          189548l
          (-3553272l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 25)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 25 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          3159746l
          (-1851402l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 26)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 26 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-2409325l)
          (-177440l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 27)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 27 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          1315589l
          1341330l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 28)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 28 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          1285669l
          (-1584928l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 29)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 29 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-812732l)
          (-1439742l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 30)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 30 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-3019102l)
          (-3881060l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 31)
      (simd_unit_ntt_at_layer_1_ (re.[ sz 31 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-3628969l)
          3839961l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  re

let simd_unit_ntt_at_layer_2_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
      (zeta: i32)
     =
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 4 ]
        <:
        i32)
      zeta
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 4)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 0 ] <: i32) -! t
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
        (sz 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 0 ] <: i32) +! t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 5 ]
        <:
        i32)
      zeta
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 5)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 1 ] <: i32) -! t
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
        (sz 1)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 1 ] <: i32) +! t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 6 ]
        <:
        i32)
      zeta
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 6)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 2 ] <: i32) -! t
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
        (sz 2)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 2 ] <: i32) +! t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 7 ]
        <:
        i32)
      zeta
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
        (sz 7)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 3 ] <: i32) -! t
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
        (sz 3)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ sz 3 ] <: i32) +! t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
  in
  simd_unit

let ntt_at_layer_2_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 0)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 0 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          2706023l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 1)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 1 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          95776l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 2)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 2 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          3077325l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 3)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 3 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          3530437l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 4)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 4 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-1661693l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 5)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 5 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-3592148l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 6)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 6 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-2537516l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 7)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 7 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          3915439l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 8)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 8 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-3861115l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 9)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 9 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-3043716l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 10)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 10 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          3574422l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 11)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 11 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-2867647l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 12)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 12 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          3539968l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 13)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 13 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-300467l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 14)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 14 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          2348700l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 15)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 15 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-539299l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 16)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 16 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-1699267l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 17)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 17 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-1643818l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 18)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 18 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          3505694l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 19)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 19 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-3821735l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 20)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 20 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          3507263l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 21)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 21 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-2140649l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 22)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 22 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-1600420l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 23)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 23 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          3699596l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 24)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 24 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          811944l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 25)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 25 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          531354l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 26)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 26 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          954230l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 27)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 27 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          3881043l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 28)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 28 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          3900724l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 29)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 29 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-2556880l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 30)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 30 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          2071892l
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      (sz 31)
      (simd_unit_ntt_at_layer_2_ (re.[ sz 31 ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          (-2797779l)
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  re

let outer_3_plus
      (v_OFFSET v_STEP_BY: usize)
      (v_ZETA: i32)
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Folds.fold_range v_OFFSET
      (v_OFFSET +! v_STEP_BY <: usize)
      (fun re temp_1_ ->
          let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re j ->
          let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) = re in
          let j:usize = j in
          let t:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
            Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_by_constant (re.[ j +!
                  v_STEP_BY
                  <:
                  usize ]
                <:
                Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
              v_ZETA
          in
          let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              (j +! v_STEP_BY <: usize)
              (Libcrux_ml_dsa.Simd.Portable.Arithmetic.subtract (re.[ j ]
                    <:
                    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
                  t
                <:
                Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          in
          let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              j
              (Libcrux_ml_dsa.Simd.Portable.Arithmetic.add (re.[ j ]
                    <:
                    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
                  t
                <:
                Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          in
          re)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  re

let ntt_at_layer_3_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 0) (sz 1) 2725464l re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 2) (sz 1) 1024112l re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 4) (sz 1) (-1079900l) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 6) (sz 1) 3585928l re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 8) (sz 1) (-549488l) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 10) (sz 1) (-1119584l) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 12) (sz 1) 2619752l re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 14) (sz 1) (-2108549l) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 16) (sz 1) (-2118186l) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 18) (sz 1) (-3859737l) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 20) (sz 1) (-1399561l) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 22) (sz 1) (-3277672l) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 24) (sz 1) 1757237l re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 26) (sz 1) (-19422l) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 28) (sz 1) 4010497l re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 30) (sz 1) 280005l re
  in
  re

let ntt_at_layer_4_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 0) (sz 2) 1826347l re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 4) (sz 2) 2353451l re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 8) (sz 2) (-359251l) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 12) (sz 2) (-2091905l) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 16) (sz 2) 3119733l re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 20) (sz 2) (-2884855l) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 24) (sz 2) 3111497l re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 28) (sz 2) 2680103l re
  in
  re

let ntt_at_layer_5_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 0) (sz 4) 237124l re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 8) (sz 4) (-777960l) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 16) (sz 4) (-876248l) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 24) (sz 4) 466468l re
  in
  re

let ntt_at_layer_6_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 0) (sz 8) (-2608894l) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 16) (sz 8) (-518909l) re
  in
  re

let ntt_at_layer_7_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    outer_3_plus (sz 0) (sz 16) 25847l re
  in
  re

let ntt (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32)) =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_7_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_6_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_5_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_4_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_3_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0_ re
  in
  re
