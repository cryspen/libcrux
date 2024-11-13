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

let ntt_at_layer_0___round
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      (index: usize)
      (zeta_0_ zeta_1_ zeta_2_ zeta_3_: i32)
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      index
      (simd_unit_ntt_at_layer_0_ (re.[ index ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          zeta_0_
          zeta_1_
          zeta_2_
          zeta_3_
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  re

let ntt_at_layer_0_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 0) 2091667l 3407706l 2316500l 3817976l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 1) (-3342478l) 2244091l (-2446433l) (-3562462l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 2) 266997l 2434439l (-1235728l) 3513181l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 3) (-3520352l) (-3759364l) (-1197226l) (-3193378l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 4) 900702l 1859098l 909542l 819034l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 5) 495491l (-1613174l) (-43260l) (-522500l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 6) (-655327l) (-3122442l) 2031748l 3207046l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 7) (-3556995l) (-525098l) (-768622l) (-3595838l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 8) 342297l 286988l (-2437823l) 4108315l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 9) 3437287l (-3342277l) 1735879l 203044l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 10) 2842341l 2691481l (-2590150l) 1265009l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 11) 4055324l 1247620l 2486353l 1595974l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 12) (-3767016l) 1250494l 2635921l (-3548272l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 13) (-2994039l) 1869119l 1903435l (-1050970l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 14) (-1333058l) 1237275l (-3318210l) (-1430225l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 15) (-451100l) 1312455l 3306115l (-1962642l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 16) (-1279661l) 1917081l (-2546312l) (-1374803l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 17) 1500165l 777191l 2235880l 3406031l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 18) (-542412l) (-2831860l) (-1671176l) (-1846953l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 19) (-2584293l) (-3724270l) 594136l (-3776993l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 20) (-2013608l) 2432395l 2454455l (-164721l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 21) 1957272l 3369112l 185531l (-1207385l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 22) (-3183426l) 162844l 1616392l 3014001l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 23) 810149l 1652634l (-3694233l) (-1799107l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 24) (-3038916l) 3523897l 3866901l 269760l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 25) 2213111l (-975884l) 1717735l 472078l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 26) (-426683l) 1723600l (-1803090l) 1910376l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 27) (-1667432l) (-1104333l) (-260646l) (-3833893l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 28) (-2939036l) (-2235985l) (-420899l) (-2286327l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 29) 183443l (-976891l) 1612842l (-3545687l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 30) (-554416l) 3919660l (-48306l) (-1362209l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_0___round re (sz 31) 3937738l 1400424l (-846154l) 1976782l
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

let ntt_at_layer_1___round
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      (index: usize)
      (zeta_0_ zeta_1_: i32)
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      index
      (simd_unit_ntt_at_layer_1_ (re.[ index ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          zeta_0_
          zeta_1_
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  re

let ntt_at_layer_1_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 0) (-3930395l) (-1528703l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 1) (-3677745l) (-3041255l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 2) (-1452451l) 3475950l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 3) 2176455l (-1585221l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 4) (-1257611l) 1939314l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 5) (-4083598l) (-1000202l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 6) (-3190144l) (-3157330l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 7) (-3632928l) 126922l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 8) 3412210l (-983419l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 9) 2147896l 2715295l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 10) (-2967645l) (-3693493l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 11) (-411027l) (-2477047l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 12) (-671102l) (-1228525l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 13) (-22981l) (-1308169l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 14) (-381987l) 1349076l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 15) 1852771l (-1430430l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 16) (-3343383l) 264944l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 17) 508951l 3097992l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 18) 44288l (-1100098l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 19) 904516l 3958618l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 20) (-3724342l) (-8578l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 21) 1653064l (-3249728l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 22) 2389356l (-210977l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 23) 759969l (-1316856l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 24) 189548l (-3553272l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 25) 3159746l (-1851402l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 26) (-2409325l) (-177440l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 27) 1315589l 1341330l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 28) 1285669l (-1584928l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 29) (-812732l) (-1439742l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 30) (-3019102l) (-3881060l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_1___round re (sz 31) (-3628969l) 3839961l
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

let ntt_at_layer_2___round
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
      (index: usize)
      (zeta: i32)
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      index
      (simd_unit_ntt_at_layer_2_ (re.[ index ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
          zeta
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  re

let ntt_at_layer_2_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 0) 2706023l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 1) 95776l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 2) 3077325l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 3) 3530437l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 4) (-1661693l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 5) (-3592148l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 6) (-2537516l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 7) 3915439l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 8) (-3861115l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 9) (-3043716l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 10) 3574422l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 11) (-2867647l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 12) 3539968l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 13) (-300467l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 14) 2348700l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 15) (-539299l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 16) (-1699267l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 17) (-1643818l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 18) 3505694l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 19) (-3821735l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 20) 3507263l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 21) (-2140649l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 22) (-1600420l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 23) 3699596l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 24) 811944l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 25) 531354l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 26) 954230l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 27) 3881043l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 28) 3900724l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 29) (-2556880l)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 30) 2071892l
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit (sz 32) =
    ntt_at_layer_2___round re (sz 31) (-2797779l)
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
