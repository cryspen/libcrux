module Libcrux_ml_dsa.Simd.Portable.Invntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Portable.Vector_type in
  ()

let simd_unit_invert_ntt_at_layer_0_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (zeta0 zeta1 zeta2 zeta3: i32)
     =
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 1 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 0 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (mk_usize 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 0 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 1 ] <: i32)
          <:
          i32)
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
        (mk_usize 1)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta0
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 3 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 2 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (mk_usize 2)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 2 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 3 ] <: i32)
          <:
          i32)
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
        (mk_usize 3)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 5 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 4 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (mk_usize 4)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 4 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 5 ] <: i32)
          <:
          i32)
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
        (mk_usize 5)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta2
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 7 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 6 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (mk_usize 6)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 6 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 7 ] <: i32)
          <:
          i32)
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
        (mk_usize 7)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta3
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  simd_unit

let simd_unit_invert_ntt_at_layer_1_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (zeta0 zeta1: i32)
     =
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 2 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 0 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (mk_usize 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 0 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 2 ] <: i32)
          <:
          i32)
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
        (mk_usize 2)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta0
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 3 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 1 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (mk_usize 1)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 1 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 3 ] <: i32)
          <:
          i32)
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
        (mk_usize 3)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta0
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 6 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 4 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (mk_usize 4)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 4 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 6 ] <: i32)
          <:
          i32)
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
        (mk_usize 6)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 7 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 5 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (mk_usize 5)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 5 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 7 ] <: i32)
          <:
          i32)
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
        (mk_usize 7)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1
          <:
          i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  simd_unit

let simd_unit_invert_ntt_at_layer_2_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (zeta: i32)
     =
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 4 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 0 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (mk_usize 0)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 0 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 4 ] <: i32)
          <:
          i32)
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
        (mk_usize 4)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32
        )
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 5 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 1 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (mk_usize 1)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 1 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 5 ] <: i32)
          <:
          i32)
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
        (mk_usize 5)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32
        )
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 6 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 2 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (mk_usize 2)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 2 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 6 ] <: i32)
          <:
          i32)
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
        (mk_usize 6)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32
        )
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  let a_minus_b:i32 =
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 7 ] <: i32) -!
    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 3 ] <: i32)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (mk_usize 3)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 3 ] <: i32) +!
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ mk_usize 7 ] <: i32)
          <:
          i32)
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
        (mk_usize 7)
        (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32
        )
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  simd_unit

let invert_ntt_at_layer_0___round
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (index: usize)
      (zeta0 zeta1 zeta2 zeta3: i32)
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      index
      (simd_unit_invert_ntt_at_layer_0_ (re.[ index ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
          zeta0
          zeta1
          zeta2
          zeta3
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
  in
  re

let invert_ntt_at_layer_0_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 0)
      (mk_i32 1976782)
      (mk_i32 (-846154))
      (mk_i32 1400424)
      (mk_i32 3937738)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 1)
      (mk_i32 (-1362209))
      (mk_i32 (-48306))
      (mk_i32 3919660)
      (mk_i32 (-554416))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 2)
      (mk_i32 (-3545687))
      (mk_i32 1612842)
      (mk_i32 (-976891))
      (mk_i32 183443)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 3)
      (mk_i32 (-2286327))
      (mk_i32 (-420899))
      (mk_i32 (-2235985))
      (mk_i32 (-2939036))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 4)
      (mk_i32 (-3833893))
      (mk_i32 (-260646))
      (mk_i32 (-1104333))
      (mk_i32 (-1667432))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 5)
      (mk_i32 1910376)
      (mk_i32 (-1803090))
      (mk_i32 1723600)
      (mk_i32 (-426683))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 6)
      (mk_i32 472078)
      (mk_i32 1717735)
      (mk_i32 (-975884))
      (mk_i32 2213111)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 7)
      (mk_i32 269760)
      (mk_i32 3866901)
      (mk_i32 3523897)
      (mk_i32 (-3038916))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 8)
      (mk_i32 (-1799107))
      (mk_i32 (-3694233))
      (mk_i32 1652634)
      (mk_i32 810149)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 9)
      (mk_i32 3014001)
      (mk_i32 1616392)
      (mk_i32 162844)
      (mk_i32 (-3183426))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 10)
      (mk_i32 (-1207385))
      (mk_i32 185531)
      (mk_i32 3369112)
      (mk_i32 1957272)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 11)
      (mk_i32 (-164721))
      (mk_i32 2454455)
      (mk_i32 2432395)
      (mk_i32 (-2013608))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 12)
      (mk_i32 (-3776993))
      (mk_i32 594136)
      (mk_i32 (-3724270))
      (mk_i32 (-2584293))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 13)
      (mk_i32 (-1846953))
      (mk_i32 (-1671176))
      (mk_i32 (-2831860))
      (mk_i32 (-542412))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 14)
      (mk_i32 3406031)
      (mk_i32 2235880)
      (mk_i32 777191)
      (mk_i32 1500165)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 15)
      (mk_i32 (-1374803))
      (mk_i32 (-2546312))
      (mk_i32 1917081)
      (mk_i32 (-1279661))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 16)
      (mk_i32 (-1962642))
      (mk_i32 3306115)
      (mk_i32 1312455)
      (mk_i32 (-451100))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 17)
      (mk_i32 (-1430225))
      (mk_i32 (-3318210))
      (mk_i32 1237275)
      (mk_i32 (-1333058))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 18)
      (mk_i32 (-1050970))
      (mk_i32 1903435)
      (mk_i32 1869119)
      (mk_i32 (-2994039))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 19)
      (mk_i32 (-3548272))
      (mk_i32 2635921)
      (mk_i32 1250494)
      (mk_i32 (-3767016))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 20)
      (mk_i32 1595974)
      (mk_i32 2486353)
      (mk_i32 1247620)
      (mk_i32 4055324)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 21)
      (mk_i32 1265009)
      (mk_i32 (-2590150))
      (mk_i32 2691481)
      (mk_i32 2842341)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 22)
      (mk_i32 203044)
      (mk_i32 1735879)
      (mk_i32 (-3342277))
      (mk_i32 3437287)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 23)
      (mk_i32 4108315)
      (mk_i32 (-2437823))
      (mk_i32 286988)
      (mk_i32 342297)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 24)
      (mk_i32 (-3595838))
      (mk_i32 (-768622))
      (mk_i32 (-525098))
      (mk_i32 (-3556995))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 25)
      (mk_i32 3207046)
      (mk_i32 2031748)
      (mk_i32 (-3122442))
      (mk_i32 (-655327))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 26)
      (mk_i32 (-522500))
      (mk_i32 (-43260))
      (mk_i32 (-1613174))
      (mk_i32 495491)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 27)
      (mk_i32 819034)
      (mk_i32 909542)
      (mk_i32 1859098)
      (mk_i32 900702)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 28)
      (mk_i32 (-3193378))
      (mk_i32 (-1197226))
      (mk_i32 (-3759364))
      (mk_i32 (-3520352))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 29)
      (mk_i32 3513181)
      (mk_i32 (-1235728))
      (mk_i32 2434439)
      (mk_i32 266997)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 30)
      (mk_i32 (-3562462))
      (mk_i32 (-2446433))
      (mk_i32 2244091)
      (mk_i32 (-3342478))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0___round re
      (mk_usize 31)
      (mk_i32 3817976)
      (mk_i32 2316500)
      (mk_i32 3407706)
      (mk_i32 2091667)
  in
  re

let invert_ntt_at_layer_1___round
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (index: usize)
      (zeta_00_ zeta_01_: i32)
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      index
      (simd_unit_invert_ntt_at_layer_1_ (re.[ index ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
          zeta_00_
          zeta_01_
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
  in
  re

let invert_ntt_at_layer_1_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 0) (mk_i32 3839961) (mk_i32 (-3628969))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 1) (mk_i32 (-3881060)) (mk_i32 (-3019102))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 2) (mk_i32 (-1439742)) (mk_i32 (-812732))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 3) (mk_i32 (-1584928)) (mk_i32 1285669)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 4) (mk_i32 1341330) (mk_i32 1315589)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 5) (mk_i32 (-177440)) (mk_i32 (-2409325))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 6) (mk_i32 (-1851402)) (mk_i32 3159746)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 7) (mk_i32 (-3553272)) (mk_i32 189548)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 8) (mk_i32 (-1316856)) (mk_i32 759969)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 9) (mk_i32 (-210977)) (mk_i32 2389356)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 10) (mk_i32 (-3249728)) (mk_i32 1653064)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 11) (mk_i32 (-8578)) (mk_i32 (-3724342))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 12) (mk_i32 3958618) (mk_i32 904516)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 13) (mk_i32 (-1100098)) (mk_i32 44288)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 14) (mk_i32 3097992) (mk_i32 508951)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 15) (mk_i32 264944) (mk_i32 (-3343383))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 16) (mk_i32 (-1430430)) (mk_i32 1852771)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 17) (mk_i32 1349076) (mk_i32 (-381987))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 18) (mk_i32 (-1308169)) (mk_i32 (-22981))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 19) (mk_i32 (-1228525)) (mk_i32 (-671102))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 20) (mk_i32 (-2477047)) (mk_i32 (-411027))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 21) (mk_i32 (-3693493)) (mk_i32 (-2967645))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 22) (mk_i32 2715295) (mk_i32 2147896)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 23) (mk_i32 (-983419)) (mk_i32 3412210)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 24) (mk_i32 126922) (mk_i32 (-3632928))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 25) (mk_i32 (-3157330)) (mk_i32 (-3190144))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 26) (mk_i32 (-1000202)) (mk_i32 (-4083598))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 27) (mk_i32 1939314) (mk_i32 (-1257611))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 28) (mk_i32 (-1585221)) (mk_i32 2176455)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 29) (mk_i32 3475950) (mk_i32 (-1452451))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 30) (mk_i32 (-3041255)) (mk_i32 (-3677745))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1___round re (mk_usize 31) (mk_i32 (-1528703)) (mk_i32 (-3930395))
  in
  re

let invert_ntt_at_layer_2___round
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (index: usize)
      (zeta1: i32)
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      index
      (simd_unit_invert_ntt_at_layer_2_ (re.[ index ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
          zeta1
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
  in
  re

let invert_ntt_at_layer_2_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 0) (mk_i32 (-2797779))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 1) (mk_i32 2071892)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 2) (mk_i32 (-2556880))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 3) (mk_i32 3900724)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 4) (mk_i32 3881043)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 5) (mk_i32 954230)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 6) (mk_i32 531354)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 7) (mk_i32 811944)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 8) (mk_i32 3699596)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 9) (mk_i32 (-1600420))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 10) (mk_i32 (-2140649))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 11) (mk_i32 3507263)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 12) (mk_i32 (-3821735))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 13) (mk_i32 3505694)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 14) (mk_i32 (-1643818))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 15) (mk_i32 (-1699267))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 16) (mk_i32 (-539299))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 17) (mk_i32 2348700)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 18) (mk_i32 (-300467))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 19) (mk_i32 3539968)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 20) (mk_i32 (-2867647))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 21) (mk_i32 3574422)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 22) (mk_i32 (-3043716))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 23) (mk_i32 (-3861115))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 24) (mk_i32 3915439)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 25) (mk_i32 (-2537516))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 26) (mk_i32 (-3592148))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 27) (mk_i32 (-1661693))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 28) (mk_i32 3530437)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 29) (mk_i32 3077325)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 30) (mk_i32 95776)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2___round re (mk_usize 31) (mk_i32 2706023)
  in
  re

let outer_3_plus
      (v_OFFSET v_STEP_BY: usize)
      (v_ZETA: i32)
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    Rust_primitives.Hax.Folds.fold_range v_OFFSET
      (v_OFFSET +! v_STEP_BY <: usize)
      (fun re temp_1_ ->
          let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
            re
          in
          let _:usize = temp_1_ in
          true)
      re
      (fun re j ->
          let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
            re
          in
          let j:usize = j in
          let rejs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            Core.Clone.f_clone #Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
              #FStar.Tactics.Typeclasses.solve
              (re.[ j +! v_STEP_BY <: usize ]
                <:
                Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
          in
          let a_minus_b:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            Core.Clone.f_clone #Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
              #FStar.Tactics.Typeclasses.solve
              rejs
          in
          let a_minus_b:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            Libcrux_ml_dsa.Simd.Portable.Arithmetic.subtract a_minus_b
              (re.[ j ] <: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
          in
          let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              j
              (Libcrux_ml_dsa.Simd.Portable.Arithmetic.add (re.[ j ]
                    <:
                    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
                  rejs
                <:
                Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
          in
          let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              (j +! v_STEP_BY <: usize)
              a_minus_b
          in
          let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              (j +! v_STEP_BY <: usize)
              (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_by_constant (re.[ j +!
                      v_STEP_BY
                      <:
                      usize ]
                    <:
                    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
                  v_ZETA
                <:
                Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
          in
          re)
  in
  re

let invert_ntt_at_layer_3_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 0) (mk_usize 1) (mk_i32 280005) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 2) (mk_usize 1) (mk_i32 4010497) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 4) (mk_usize 1) (mk_i32 (-19422)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 6) (mk_usize 1) (mk_i32 1757237) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 8) (mk_usize 1) (mk_i32 (-3277672)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 10) (mk_usize 1) (mk_i32 (-1399561)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 12) (mk_usize 1) (mk_i32 (-3859737)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 14) (mk_usize 1) (mk_i32 (-2118186)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 16) (mk_usize 1) (mk_i32 (-2108549)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 18) (mk_usize 1) (mk_i32 2619752) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 20) (mk_usize 1) (mk_i32 (-1119584)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 22) (mk_usize 1) (mk_i32 (-549488)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 24) (mk_usize 1) (mk_i32 3585928) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 26) (mk_usize 1) (mk_i32 (-1079900)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 28) (mk_usize 1) (mk_i32 1024112) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 30) (mk_usize 1) (mk_i32 2725464) re
  in
  re

let invert_ntt_at_layer_4_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 0) (mk_usize 2) (mk_i32 2680103) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 4) (mk_usize 2) (mk_i32 3111497) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 8) (mk_usize 2) (mk_i32 (-2884855)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 12) (mk_usize 2) (mk_i32 3119733) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 16) (mk_usize 2) (mk_i32 (-2091905)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 20) (mk_usize 2) (mk_i32 (-359251)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 24) (mk_usize 2) (mk_i32 2353451) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 28) (mk_usize 2) (mk_i32 1826347) re
  in
  re

let invert_ntt_at_layer_5_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 0) (mk_usize 4) (mk_i32 466468) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 8) (mk_usize 4) (mk_i32 (-876248)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 16) (mk_usize 4) (mk_i32 (-777960)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 24) (mk_usize 4) (mk_i32 237124) re
  in
  re

let invert_ntt_at_layer_6_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 0) (mk_usize 8) (mk_i32 (-518909)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 16) (mk_usize 8) (mk_i32 (-2608894)) re
  in
  re

let invert_ntt_at_layer_7_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 0) (mk_usize 16) (mk_i32 25847) re
  in
  re

let invert_ntt_montgomery
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
     =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_0_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_1_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_2_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_3_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_4_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_5_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_6_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    invert_ntt_at_layer_7_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          (re <: t_Slice Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        <:
        usize)
      (fun re temp_1_ ->
          let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
            re
          in
          let _:usize = temp_1_ in
          true)
      re
      (fun re i ->
          let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
            re
          in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
            i
            (Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_by_constant (re.[ i ]
                  <:
                  Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
                (mk_i32 41978)
              <:
              Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
          <:
          t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
  in
  re
