module Libcrux_ml_dsa.Simd.Portable.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let invert_ntt_at_layer_0_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
      (zeta0 zeta1 zeta2 zeta3: i32)
     =
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 1 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 0 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 0 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 1 ] <: i32)
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
        (sz 1)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta0
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 3 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 2 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 2)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 2 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 3 ] <: i32)
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
        (sz 3)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 5 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 4 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 4)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 4 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 5 ] <: i32)
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
        (sz 5)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta2
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 7 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 6 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 6)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 6 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 7 ] <: i32)
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
        (sz 7)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta3
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  simd_unit

let invert_ntt_at_layer_1_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
      (zeta0 zeta1: i32)
     =
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 2 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 0 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 0 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 2 ] <: i32)
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
        (sz 2)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta0
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 3 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 1 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 1)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 1 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 3 ] <: i32)
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
        (sz 3)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta0
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 6 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 4 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 4)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 4 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 6 ] <: i32)
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
        (sz 6)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 7 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 5 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 5)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 5 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 7 ] <: i32)
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
        (sz 7)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  simd_unit

let invert_ntt_at_layer_2_ (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit) (zeta: i32) =
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 4 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 0 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 0 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 4 ] <: i32)
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
        (sz 4)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32
        )
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 5 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 1 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 1)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 1 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 5 ] <: i32)
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
        (sz 5)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32
        )
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 6 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 2 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 2)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 2 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 6 ] <: i32)
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
        (sz 6)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32
        )
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 7 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 3 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 3)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 3 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 7 ] <: i32)
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
        (sz 7)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32
        )
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  simd_unit

let ntt_at_layer_0_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
      (zeta0 zeta1 zeta2 zeta3: i32)
     =
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 1 ]
        <:
        i32)
      zeta0
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 1)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 0 ] <: i32) -! t <: i32)
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
        (sz 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 0 ] <: i32) +! t <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 3 ]
        <:
        i32)
      zeta1
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 3)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 2 ] <: i32) -! t <: i32)
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
        (sz 2)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 2 ] <: i32) +! t <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 5 ]
        <:
        i32)
      zeta2
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 5)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 4 ] <: i32) -! t <: i32)
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
        (sz 4)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 4 ] <: i32) +! t <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 7 ]
        <:
        i32)
      zeta3
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 7)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 6 ] <: i32) -! t <: i32)
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
        (sz 6)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 6 ] <: i32) +! t <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  simd_unit

let ntt_at_layer_1_ (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit) (zeta1 zeta2: i32) =
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 2 ]
        <:
        i32)
      zeta1
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 2)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 0 ] <: i32) -! t <: i32)
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
        (sz 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 0 ] <: i32) +! t <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 3 ]
        <:
        i32)
      zeta1
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 3)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 1 ] <: i32) -! t <: i32)
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
        (sz 1)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 1 ] <: i32) +! t <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 6 ]
        <:
        i32)
      zeta2
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 6)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 4 ] <: i32) -! t <: i32)
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
        (sz 4)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 4 ] <: i32) +! t <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 7 ]
        <:
        i32)
      zeta2
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 7)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 5 ] <: i32) -! t <: i32)
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
        (sz 5)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 5 ] <: i32) +! t <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  simd_unit

let ntt_at_layer_2_ (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit) (zeta: i32) =
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 4 ]
        <:
        i32)
      zeta
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 4)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 0 ] <: i32) -! t <: i32)
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
        (sz 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 0 ] <: i32) +! t <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 5 ]
        <:
        i32)
      zeta
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 5)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 1 ] <: i32) -! t <: i32)
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
        (sz 1)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 1 ] <: i32) +! t <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 6 ]
        <:
        i32)
      zeta
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 6)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 2 ] <: i32) -! t <: i32)
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
        (sz 2)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 2 ] <: i32) +! t <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 7 ]
        <:
        i32)
      zeta
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (sz 7)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 3 ] <: i32) -! t <: i32)
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
        (sz 3)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ sz 3 ] <: i32) +! t <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  simd_unit
