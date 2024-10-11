module Libcrux_ml_dsa.Simd.Portable.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Portable in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let invert_ntt_at_layer_0_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
      (zeta0 zeta1 zeta2 zeta3: i32)
    : Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 1 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 0 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (Rust_primitives.mk_usize 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 0 ]
            <:
            i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 1 ]
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
        (Rust_primitives.mk_usize 1)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta0
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 3 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 2 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (Rust_primitives.mk_usize 2)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 2 ]
            <:
            i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 3 ]
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
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 5 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 4 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (Rust_primitives.mk_usize 4)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 4 ]
            <:
            i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 5 ]
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
        (Rust_primitives.mk_usize 5)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta2
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 7 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 6 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (Rust_primitives.mk_usize 6)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 6 ]
            <:
            i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 7 ]
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
        (Rust_primitives.mk_usize 7)
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
    : Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 2 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 0 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (Rust_primitives.mk_usize 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 0 ]
            <:
            i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 2 ]
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
        (Rust_primitives.mk_usize 2)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta0
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 3 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 1 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (Rust_primitives.mk_usize 1)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 1 ]
            <:
            i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 3 ]
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
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta0
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 6 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 4 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (Rust_primitives.mk_usize 4)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 4 ]
            <:
            i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 6 ]
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
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 7 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 5 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (Rust_primitives.mk_usize 5)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 5 ]
            <:
            i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 7 ]
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
        (Rust_primitives.mk_usize 7)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  simd_unit

let invert_ntt_at_layer_2_ (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit) (zeta: i32)
    : Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 4 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 0 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (Rust_primitives.mk_usize 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 0 ]
            <:
            i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 4 ]
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
        (Rust_primitives.mk_usize 4)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32
        )
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 5 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 1 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (Rust_primitives.mk_usize 1)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 1 ]
            <:
            i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 5 ]
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
        (Rust_primitives.mk_usize 5)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32
        )
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 6 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 2 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (Rust_primitives.mk_usize 2)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 2 ]
            <:
            i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 6 ]
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
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32
        )
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 7 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 3 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients
        (Rust_primitives.mk_usize 3)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 3 ]
            <:
            i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 7 ]
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
        (Rust_primitives.mk_usize 7)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32
        )
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  simd_unit

let simd_unit_ntt_at_layer_0_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
      (zeta0 zeta1 zeta2 zeta3: i32)
    : Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 1 ]
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
        (Rust_primitives.mk_usize 1)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 0 ]
            <:
            i32) -!
          t
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
        (Rust_primitives.mk_usize 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 0 ]
            <:
            i32) +!
          t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 3 ]
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
        (Rust_primitives.mk_usize 3)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 2 ]
            <:
            i32) -!
          t
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
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 2 ]
            <:
            i32) +!
          t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 5 ]
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
        (Rust_primitives.mk_usize 5)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 4 ]
            <:
            i32) -!
          t
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
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 4 ]
            <:
            i32) +!
          t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 7 ]
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
        (Rust_primitives.mk_usize 7)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 6 ]
            <:
            i32) -!
          t
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
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 6 ]
            <:
            i32) +!
          t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  simd_unit

let ntt_at_layer_0_
      (zeta_i: usize)
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32))
    : (usize & t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32)
    ) =
  let zeta_i:usize = zeta_i +! Rust_primitives.mk_usize 1 in
  let re, zeta_i:(t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      (Rust_primitives.mk_usize 32) &
    usize) =
    Rust_primitives.Hax.Folds.fold_range (Rust_primitives.mk_usize 0)
      (Core.Slice.impl__len #Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          (re <: t_Slice Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
        <:
        usize)
      (fun temp_0_ temp_1_ ->
          let re, zeta_i:(t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
              (Rust_primitives.mk_usize 32) &
            usize) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (re, zeta_i
        <:
        (t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32) &
          usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
              (Rust_primitives.mk_usize 32) &
            usize) =
            temp_0_
          in
          let round:usize = round in
          let re:t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
            (Rust_primitives.mk_usize 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              round
              (simd_unit_ntt_at_layer_0_ (re.[ round ]
                    <:
                    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
                  (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                  (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +!
                      Rust_primitives.mk_usize 1
                      <:
                      usize ]
                    <:
                    i32)
                  (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +!
                      Rust_primitives.mk_usize 2
                      <:
                      usize ]
                    <:
                    i32)
                  (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +!
                      Rust_primitives.mk_usize 3
                      <:
                      usize ]
                    <:
                    i32)
                <:
                Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
          in
          let zeta_i:usize = zeta_i +! Rust_primitives.mk_usize 4 in
          re, zeta_i
          <:
          (t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32) &
            usize))
  in
  let zeta_i:usize = zeta_i -! Rust_primitives.mk_usize 1 in
  zeta_i, re
  <:
  (usize & t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32))

let simd_unit_ntt_at_layer_1_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
      (zeta1 zeta2: i32)
    : Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 2 ]
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
        (Rust_primitives.mk_usize 2)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 0 ]
            <:
            i32) -!
          t
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
        (Rust_primitives.mk_usize 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 0 ]
            <:
            i32) +!
          t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 3 ]
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
        (Rust_primitives.mk_usize 3)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 1 ]
            <:
            i32) -!
          t
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
        (Rust_primitives.mk_usize 1)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 1 ]
            <:
            i32) +!
          t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 6 ]
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
        (Rust_primitives.mk_usize 6)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 4 ]
            <:
            i32) -!
          t
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
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 4 ]
            <:
            i32) +!
          t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 7 ]
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
        (Rust_primitives.mk_usize 7)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 5 ]
            <:
            i32) -!
          t
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
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 5 ]
            <:
            i32) +!
          t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  simd_unit

let ntt_at_layer_1_
      (zeta_i: usize)
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32))
    : (usize & t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32)
    ) =
  let zeta_i:usize = zeta_i +! Rust_primitives.mk_usize 1 in
  let re, zeta_i:(t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      (Rust_primitives.mk_usize 32) &
    usize) =
    Rust_primitives.Hax.Folds.fold_range (Rust_primitives.mk_usize 0)
      (Core.Slice.impl__len #Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          (re <: t_Slice Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
        <:
        usize)
      (fun temp_0_ temp_1_ ->
          let re, zeta_i:(t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
              (Rust_primitives.mk_usize 32) &
            usize) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (re, zeta_i
        <:
        (t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32) &
          usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
              (Rust_primitives.mk_usize 32) &
            usize) =
            temp_0_
          in
          let round:usize = round in
          let re:t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
            (Rust_primitives.mk_usize 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              round
              (simd_unit_ntt_at_layer_1_ (re.[ round ]
                    <:
                    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
                  (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                  (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +!
                      Rust_primitives.mk_usize 1
                      <:
                      usize ]
                    <:
                    i32)
                <:
                Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
          in
          let zeta_i:usize = zeta_i +! Rust_primitives.mk_usize 2 in
          re, zeta_i
          <:
          (t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32) &
            usize))
  in
  let zeta_i:usize = zeta_i -! Rust_primitives.mk_usize 1 in
  zeta_i, re
  <:
  (usize & t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32))

let simd_unit_ntt_at_layer_2_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
      (zeta: i32)
    : Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 4 ]
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
        (Rust_primitives.mk_usize 4)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 0 ]
            <:
            i32) -!
          t
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
        (Rust_primitives.mk_usize 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 0 ]
            <:
            i32) +!
          t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 5 ]
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
        (Rust_primitives.mk_usize 5)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 1 ]
            <:
            i32) -!
          t
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
        (Rust_primitives.mk_usize 1)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 1 ]
            <:
            i32) +!
          t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 6 ]
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
        (Rust_primitives.mk_usize 6)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 2 ]
            <:
            i32) -!
          t
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
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 2 ]
            <:
            i32) +!
          t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 7 ]
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
        (Rust_primitives.mk_usize 7)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 3 ]
            <:
            i32) -!
          t
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
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 3 ]
            <:
            i32) +!
          t
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
  in
  simd_unit

let ntt_at_layer_2_
      (zeta_i: usize)
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32))
    : (usize & t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32)
    ) =
  let (re, zeta_i), hax_temp_output:(t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      (Rust_primitives.mk_usize 32) &
    usize) =
    Rust_primitives.Hax.Folds.fold_range (Rust_primitives.mk_usize 0)
      (Core.Slice.impl__len #Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          (re <: t_Slice Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
        <:
        usize)
      (fun temp_0_ temp_1_ ->
          let re, zeta_i:(t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
              (Rust_primitives.mk_usize 32) &
            usize) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (re, zeta_i
        <:
        (t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32) &
          usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
              (Rust_primitives.mk_usize 32) &
            usize) =
            temp_0_
          in
          let round:usize = round in
          let zeta_i:usize = zeta_i +! Rust_primitives.mk_usize 1 in
          let re:t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
            (Rust_primitives.mk_usize 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              round
              (simd_unit_ntt_at_layer_2_ (re.[ round ]
                    <:
                    Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
                  (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                <:
                Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
          in
          re, zeta_i
          <:
          (t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32) &
            usize))
  in
  zeta_i, re
  <:
  (usize & t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32))

let ntt (re: t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32))
    : t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32) =
  let zeta_i:usize = Rust_primitives.mk_usize 0 in
  let tmp0, tmp1:(usize &
    t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32)) =
    ntt_at_layer_3_plus (Rust_primitives.mk_usize 7) zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32) =
    tmp1
  in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize &
    t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32)) =
    ntt_at_layer_3_plus (Rust_primitives.mk_usize 6) zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32) =
    tmp1
  in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize &
    t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32)) =
    ntt_at_layer_3_plus (Rust_primitives.mk_usize 5) zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32) =
    tmp1
  in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize &
    t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32)) =
    ntt_at_layer_3_plus (Rust_primitives.mk_usize 4) zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32) =
    tmp1
  in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize &
    t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32)) =
    ntt_at_layer_3_plus (Rust_primitives.mk_usize 3) zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32) =
    tmp1
  in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize &
    t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32)) =
    ntt_at_layer_2_ zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32) =
    tmp1
  in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize &
    t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32)) =
    ntt_at_layer_1_ zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32) =
    tmp1
  in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize &
    t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32)) =
    ntt_at_layer_0_ zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32) =
    tmp1
  in
  let _:Prims.unit = () in
  re

let ntt_at_layer_3_plus
      (v_LAYER zeta_i: usize)
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32))
    : (usize & t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32)
    ) =
  let step:usize = Rust_primitives.mk_usize 1 <<! v_LAYER in
  let (re, zeta_i), hax_temp_output:(t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      (Rust_primitives.mk_usize 32) &
    usize) =
    Rust_primitives.Hax.Folds.fold_range (Rust_primitives.mk_usize 0)
      (Rust_primitives.mk_usize 128 >>! v_LAYER <: usize)
      (fun temp_0_ temp_1_ ->
          let re, zeta_i:(t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
              (Rust_primitives.mk_usize 32) &
            usize) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (re, zeta_i
        <:
        (t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32) &
          usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
              (Rust_primitives.mk_usize 32) &
            usize) =
            temp_0_
          in
          let round:usize = round in
          let zeta_i:usize = zeta_i +! Rust_primitives.mk_usize 1 in
          let offset:usize =
            ((round *! step <: usize) *! Rust_primitives.mk_usize 2 <: usize) /!
            Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT
          in
          let step_by:usize = step /! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT in
          let re:t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
            (Rust_primitives.mk_usize 32) =
            Rust_primitives.Hax.Folds.fold_range offset
              (offset +! step_by <: usize)
              (fun re temp_1_ ->
                  let re:t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
                    (Rust_primitives.mk_usize 32) =
                    re
                  in
                  let _:usize = temp_1_ in
                  true)
              re
              (fun re j ->
                  let re:t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
                    (Rust_primitives.mk_usize 32) =
                    re
                  in
                  let j:usize = j in
                  let t:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
                    Libcrux_ml_dsa.Simd.Traits.montgomery_multiply_by_fer #Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
                      (re.[ j +! step_by <: usize ]
                        <:
                        Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
                      (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                  in
                  let re:t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
                    (Rust_primitives.mk_usize 32) =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                      (j +! step_by <: usize)
                      (Libcrux_ml_dsa.Simd.Portable.Arithmetic.subtract (re.[ j ]
                            <:
                            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
                          t
                        <:
                        Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
                  in
                  let re:t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
                    (Rust_primitives.mk_usize 32) =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                      j
                      (Libcrux_ml_dsa.Simd.Portable.Arithmetic.add (re.[ j ]
                            <:
                            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
                          t
                        <:
                        Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
                  in
                  re)
          in
          re, zeta_i
          <:
          (t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32) &
            usize))
  in
  zeta_i, re
  <:
  (usize & t_Array Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit (Rust_primitives.mk_usize 32))
