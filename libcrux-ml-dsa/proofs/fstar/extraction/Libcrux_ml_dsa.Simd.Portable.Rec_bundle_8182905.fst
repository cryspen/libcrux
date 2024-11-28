module Libcrux_ml_dsa.Simd.Portable.Rec_bundle_8182905
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Portable in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

type t_PortableSIMDUnit = { f_coefficients:t_Array i32 (sz 8) }

let v_MONTGOMERY_SHIFT: u8 = 32uy

let compute_one_hint (v_GAMMA2 low high: i32) : i32 =
  if
    low >. v_GAMMA2 || low <. (Core.Ops.Arith.Neg.neg v_GAMMA2 <: i32) ||
    low =. (Core.Ops.Arith.Neg.neg v_GAMMA2 <: i32) && high <>. 0l
  then 1l
  else 0l

let get_n_least_significant_bits (n: u8) (value: u64) : u64 =
  value &. ((1uL <<! n <: u64) -! 1uL <: u64)

let v_ETA832233724: i32 = 2l

let v_ETA177254429: i32 = 4l

let v_ETA345140054: i32 = 2l

let v_ETA858068178: i32 = 4l

let v_GAMMA1183990813: i32 = 1l <<! 17l

let v_GAMMA1_TIMES_2_BITMASK305664693: i32 = (v_GAMMA1183990813 <<! 1l <: i32) -! 1l

let v_GAMMA1465203885: i32 = 1l <<! 19l

let v_GAMMA1_TIMES_2_BITMASK614047129: i32 = (v_GAMMA1465203885 <<! 1l <: i32) -! 1l

let v_GAMMA1331343739: i32 = 1l <<! 17l

let v_GAMMA1658756807: i32 = 1l <<! 19l

let change_t0_interval (t0: i32) : i32 =
  (1l <<! (Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T -! sz 1 <: usize) <: i32) -! t0

let v_BITS_IN_LOWER_PART_OF_T_MASK: i32 =
  (1l <<! (cast (Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T <: usize) <: i32) <: i32) -! 1l

let reduce_element (fe: i32) : i32 =
  let quotient:i32 = (fe +! (1l <<! 22l <: i32) <: i32) >>! 23l in
  fe -! (quotient *! Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32)

let montgomery_reduce_element (value: i64) : i32 =
  let t:u64 =
    (get_n_least_significant_bits v_MONTGOMERY_SHIFT (cast (value <: i64) <: u64) <: u64) *!
    Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
  in
  let k:i32 = cast (get_n_least_significant_bits v_MONTGOMERY_SHIFT t <: u64) <: i32 in
  let k_times_modulus:i64 =
    (cast (k <: i32) <: i64) *! (cast (Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32) <: i64)
  in
  let c:i32 = cast (k_times_modulus >>! v_MONTGOMERY_SHIFT <: i64) <: i32 in
  let value_high:i32 = cast (value >>! v_MONTGOMERY_SHIFT <: i64) <: i32 in
  value_high -! c

let montgomery_multiply_fe_by_fer (fe fer: i32) : i32 =
  montgomery_reduce_element ((cast (fe <: i32) <: i64) *! (cast (fer <: i32) <: i64) <: i64)

let invert_ntt_at_layer_0_ (simd_unit: t_PortableSIMDUnit) (zeta0 zeta1 zeta2 zeta3: i32)
    : t_PortableSIMDUnit =
  let a_minus_b:i32 =
    (simd_unit.f_coefficients.[ sz 1 ] <: i32) -! (simd_unit.f_coefficients.[ sz 0 ] <: i32)
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 0)
        ((simd_unit.f_coefficients.[ sz 0 ] <: i32) +! (simd_unit.f_coefficients.[ sz 1 ] <: i32)
          <:
          i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 1)
        (montgomery_multiply_fe_by_fer a_minus_b zeta0 <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.f_coefficients.[ sz 3 ] <: i32) -! (simd_unit.f_coefficients.[ sz 2 ] <: i32)
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 2)
        ((simd_unit.f_coefficients.[ sz 2 ] <: i32) +! (simd_unit.f_coefficients.[ sz 3 ] <: i32)
          <:
          i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 3)
        (montgomery_multiply_fe_by_fer a_minus_b zeta1 <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.f_coefficients.[ sz 5 ] <: i32) -! (simd_unit.f_coefficients.[ sz 4 ] <: i32)
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 4)
        ((simd_unit.f_coefficients.[ sz 4 ] <: i32) +! (simd_unit.f_coefficients.[ sz 5 ] <: i32)
          <:
          i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 5)
        (montgomery_multiply_fe_by_fer a_minus_b zeta2 <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.f_coefficients.[ sz 7 ] <: i32) -! (simd_unit.f_coefficients.[ sz 6 ] <: i32)
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 6)
        ((simd_unit.f_coefficients.[ sz 6 ] <: i32) +! (simd_unit.f_coefficients.[ sz 7 ] <: i32)
          <:
          i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 7)
        (montgomery_multiply_fe_by_fer a_minus_b zeta3 <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  simd_unit

let invert_ntt_at_layer_1_ (simd_unit: t_PortableSIMDUnit) (zeta0 zeta1: i32) : t_PortableSIMDUnit =
  let a_minus_b:i32 =
    (simd_unit.f_coefficients.[ sz 2 ] <: i32) -! (simd_unit.f_coefficients.[ sz 0 ] <: i32)
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 0)
        ((simd_unit.f_coefficients.[ sz 0 ] <: i32) +! (simd_unit.f_coefficients.[ sz 2 ] <: i32)
          <:
          i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 2)
        (montgomery_multiply_fe_by_fer a_minus_b zeta0 <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.f_coefficients.[ sz 3 ] <: i32) -! (simd_unit.f_coefficients.[ sz 1 ] <: i32)
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 1)
        ((simd_unit.f_coefficients.[ sz 1 ] <: i32) +! (simd_unit.f_coefficients.[ sz 3 ] <: i32)
          <:
          i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 3)
        (montgomery_multiply_fe_by_fer a_minus_b zeta0 <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.f_coefficients.[ sz 6 ] <: i32) -! (simd_unit.f_coefficients.[ sz 4 ] <: i32)
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 4)
        ((simd_unit.f_coefficients.[ sz 4 ] <: i32) +! (simd_unit.f_coefficients.[ sz 6 ] <: i32)
          <:
          i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 6)
        (montgomery_multiply_fe_by_fer a_minus_b zeta1 <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.f_coefficients.[ sz 7 ] <: i32) -! (simd_unit.f_coefficients.[ sz 5 ] <: i32)
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 5)
        ((simd_unit.f_coefficients.[ sz 5 ] <: i32) +! (simd_unit.f_coefficients.[ sz 7 ] <: i32)
          <:
          i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 7)
        (montgomery_multiply_fe_by_fer a_minus_b zeta1 <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  simd_unit

let invert_ntt_at_layer_2_ (simd_unit: t_PortableSIMDUnit) (zeta: i32) : t_PortableSIMDUnit =
  let a_minus_b:i32 =
    (simd_unit.f_coefficients.[ sz 4 ] <: i32) -! (simd_unit.f_coefficients.[ sz 0 ] <: i32)
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 0)
        ((simd_unit.f_coefficients.[ sz 0 ] <: i32) +! (simd_unit.f_coefficients.[ sz 4 ] <: i32)
          <:
          i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 4)
        (montgomery_multiply_fe_by_fer a_minus_b zeta <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.f_coefficients.[ sz 5 ] <: i32) -! (simd_unit.f_coefficients.[ sz 1 ] <: i32)
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 1)
        ((simd_unit.f_coefficients.[ sz 1 ] <: i32) +! (simd_unit.f_coefficients.[ sz 5 ] <: i32)
          <:
          i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 5)
        (montgomery_multiply_fe_by_fer a_minus_b zeta <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.f_coefficients.[ sz 6 ] <: i32) -! (simd_unit.f_coefficients.[ sz 2 ] <: i32)
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 2)
        ((simd_unit.f_coefficients.[ sz 2 ] <: i32) +! (simd_unit.f_coefficients.[ sz 6 ] <: i32)
          <:
          i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 6)
        (montgomery_multiply_fe_by_fer a_minus_b zeta <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let a_minus_b:i32 =
    (simd_unit.f_coefficients.[ sz 7 ] <: i32) -! (simd_unit.f_coefficients.[ sz 3 ] <: i32)
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 3)
        ((simd_unit.f_coefficients.[ sz 3 ] <: i32) +! (simd_unit.f_coefficients.[ sz 7 ] <: i32)
          <:
          i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 7)
        (montgomery_multiply_fe_by_fer a_minus_b zeta <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  simd_unit

let simd_unit_ntt_at_layer_0_ (simd_unit: t_PortableSIMDUnit) (zeta0 zeta1 zeta2 zeta3: i32)
    : t_PortableSIMDUnit =
  let t:i32 = montgomery_multiply_fe_by_fer (simd_unit.f_coefficients.[ sz 1 ] <: i32) zeta0 in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 1)
        ((simd_unit.f_coefficients.[ sz 0 ] <: i32) -! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 0)
        ((simd_unit.f_coefficients.[ sz 0 ] <: i32) +! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let t:i32 = montgomery_multiply_fe_by_fer (simd_unit.f_coefficients.[ sz 3 ] <: i32) zeta1 in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 3)
        ((simd_unit.f_coefficients.[ sz 2 ] <: i32) -! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 2)
        ((simd_unit.f_coefficients.[ sz 2 ] <: i32) +! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let t:i32 = montgomery_multiply_fe_by_fer (simd_unit.f_coefficients.[ sz 5 ] <: i32) zeta2 in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 5)
        ((simd_unit.f_coefficients.[ sz 4 ] <: i32) -! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 4)
        ((simd_unit.f_coefficients.[ sz 4 ] <: i32) +! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let t:i32 = montgomery_multiply_fe_by_fer (simd_unit.f_coefficients.[ sz 7 ] <: i32) zeta3 in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 7)
        ((simd_unit.f_coefficients.[ sz 6 ] <: i32) -! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 6)
        ((simd_unit.f_coefficients.[ sz 6 ] <: i32) +! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  simd_unit

let simd_unit_ntt_at_layer_1_ (simd_unit: t_PortableSIMDUnit) (zeta1 zeta2: i32)
    : t_PortableSIMDUnit =
  let t:i32 = montgomery_multiply_fe_by_fer (simd_unit.f_coefficients.[ sz 2 ] <: i32) zeta1 in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 2)
        ((simd_unit.f_coefficients.[ sz 0 ] <: i32) -! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 0)
        ((simd_unit.f_coefficients.[ sz 0 ] <: i32) +! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let t:i32 = montgomery_multiply_fe_by_fer (simd_unit.f_coefficients.[ sz 3 ] <: i32) zeta1 in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 3)
        ((simd_unit.f_coefficients.[ sz 1 ] <: i32) -! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 1)
        ((simd_unit.f_coefficients.[ sz 1 ] <: i32) +! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let t:i32 = montgomery_multiply_fe_by_fer (simd_unit.f_coefficients.[ sz 6 ] <: i32) zeta2 in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 6)
        ((simd_unit.f_coefficients.[ sz 4 ] <: i32) -! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 4)
        ((simd_unit.f_coefficients.[ sz 4 ] <: i32) +! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let t:i32 = montgomery_multiply_fe_by_fer (simd_unit.f_coefficients.[ sz 7 ] <: i32) zeta2 in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 7)
        ((simd_unit.f_coefficients.[ sz 5 ] <: i32) -! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 5)
        ((simd_unit.f_coefficients.[ sz 5 ] <: i32) +! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  simd_unit

let simd_unit_ntt_at_layer_2_ (simd_unit: t_PortableSIMDUnit) (zeta: i32) : t_PortableSIMDUnit =
  let t:i32 = montgomery_multiply_fe_by_fer (simd_unit.f_coefficients.[ sz 4 ] <: i32) zeta in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 4)
        ((simd_unit.f_coefficients.[ sz 0 ] <: i32) -! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 0)
        ((simd_unit.f_coefficients.[ sz 0 ] <: i32) +! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let t:i32 = montgomery_multiply_fe_by_fer (simd_unit.f_coefficients.[ sz 5 ] <: i32) zeta in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 5)
        ((simd_unit.f_coefficients.[ sz 1 ] <: i32) -! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 1)
        ((simd_unit.f_coefficients.[ sz 1 ] <: i32) +! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let t:i32 = montgomery_multiply_fe_by_fer (simd_unit.f_coefficients.[ sz 6 ] <: i32) zeta in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 6)
        ((simd_unit.f_coefficients.[ sz 2 ] <: i32) -! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 2)
        ((simd_unit.f_coefficients.[ sz 2 ] <: i32) +! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let t:i32 = montgomery_multiply_fe_by_fer (simd_unit.f_coefficients.[ sz 7 ] <: i32) zeta in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 7)
        ((simd_unit.f_coefficients.[ sz 3 ] <: i32) -! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 3)
        ((simd_unit.f_coefficients.[ sz 3 ] <: i32) +! t <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  simd_unit

let decompose_element (v_GAMMA2 r: i32) : (i32 & i32) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.((r >. (Core.Ops.Arith.Neg.neg Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32)
              <:
              bool) &&
            (r <. Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1 (sz 1)
                    (sz 1)
                    (let list = ["the representative is "] in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list 1 list)
                    (let list =
                        [Core.Fmt.Rt.impl_1__new_display #i32 r <: Core.Fmt.Rt.t_Argument]
                      in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list 1 list)
                  <:
                  Core.Fmt.t_Arguments)
              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let r:i32 = r +! ((r >>! 31l <: i32) &. Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32) in
  let v_ALPHA:i32 = v_GAMMA2 *! 2l in
  let ceil_of_r_by_128_:i32 = (r +! 127l <: i32) >>! 7l in
  let r1:i32 =
    match v_ALPHA with
    | 190464l ->
      let result:i32 =
        ((ceil_of_r_by_128_ *! 11275l <: i32) +! (1l <<! 23l <: i32) <: i32) >>! 24l
      in
      (result ^. ((43l -! result <: i32) >>! 31l <: i32) <: i32) &. result
    | 523776l ->
      let result:i32 =
        ((ceil_of_r_by_128_ *! 1025l <: i32) +! (1l <<! 21l <: i32) <: i32) >>! 22l
      in
      result &. 15l
    | _ ->
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

          <:
          Rust_primitives.Hax.t_Never)
  in
  let r0:i32 = r -! (r1 *! v_ALPHA <: i32) in
  let r0:i32 =
    r0 -!
    (((((Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS -! 1l <: i32) /! 2l <: i32) -! r0 <: i32) >>!
        31l
        <:
        i32) &.
      Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
      <:
      i32)
  in
  r0, r1 <: (i32 & i32)

let infinity_norm_exceeds (simd_unit: t_PortableSIMDUnit) (bound: i32) : bool =
  let exceeds:bool = false in
  let exceeds:bool =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Array.Iter.t_IntoIter
              i32 (sz 8))
          #FStar.Tactics.Typeclasses.solve
          (Core.Iter.Traits.Collect.f_into_iter #(t_Array i32 (sz 8))
              #FStar.Tactics.Typeclasses.solve
              simd_unit.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 8))
        <:
        Core.Array.Iter.t_IntoIter i32 (sz 8))
      exceeds
      (fun exceeds coefficient ->
          let exceeds:bool = exceeds in
          let coefficient:i32 = coefficient in
          let _:Prims.unit =
            if true
            then
              let _:Prims.unit =
                if
                  ~.((coefficient >.
                      (Core.Ops.Arith.Neg.neg Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32)
                      <:
                      bool) &&
                    (coefficient <. Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: bool))
                then
                  Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1
                            (sz 1)
                            (sz 1)
                            (let list = ["coefficient is "] in
                              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                              Rust_primitives.Hax.array_of_list 1 list)
                            (let list =
                                [
                                  Core.Fmt.Rt.impl_1__new_display #i32 coefficient
                                  <:
                                  Core.Fmt.Rt.t_Argument
                                ]
                              in
                              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                              Rust_primitives.Hax.array_of_list 1 list)
                          <:
                          Core.Fmt.t_Arguments)
                      <:
                      Rust_primitives.Hax.t_Never)
              in
              ()
          in
          let sign:i32 = coefficient >>! 31l in
          let normalized:i32 = coefficient -! (sign &. (2l *! coefficient <: i32) <: i32) in
          let exceeds:bool = exceeds |. (normalized >=. bound <: bool) in
          exceeds)
  in
  exceeds

let power2round_element (t: i32) : (i32 & i32) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.((t >. (Core.Ops.Arith.Neg.neg Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32)
              <:
              bool) &&
            (t <. Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1 (sz 1)
                    (sz 1)
                    (let list = ["t is "] in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list 1 list)
                    (let list =
                        [Core.Fmt.Rt.impl_1__new_display #i32 t <: Core.Fmt.Rt.t_Argument]
                      in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list 1 list)
                  <:
                  Core.Fmt.t_Arguments)
              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let t:i32 = t +! ((t >>! 31l <: i32) &. Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32) in
  let t1:i32 =
    ((t -! 1l <: i32) +!
      (1l <<! (Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T -! sz 1 <: usize) <: i32)
      <:
      i32) >>!
    Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T
  in
  let t0:i32 = t -! (t1 <<! Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T <: i32) in
  t0, t1 <: (i32 & i32)

let use_one_hint (v_GAMMA2 r hint: i32) : i32 =
  let r0, r1:(i32 & i32) = decompose_element v_GAMMA2 r in
  if hint =. 0l
  then r1
  else
    match v_GAMMA2 with
    | 95232l ->
      if r0 >. 0l
      then if r1 =. 43l then 0l else r1 +! hint
      else if r1 =. 0l then 43l else r1 -! hint
    | 261888l -> if r0 >. 0l then (r1 +! hint <: i32) &. 15l else (r1 -! hint <: i32) &. 15l
    | _ ->
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

          <:
          Rust_primitives.Hax.t_Never)

let serialize_when_eta_is_2_ (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit)
    : t_Array u8 v_OUTPUT_SIZE =
  let serialized:t_Array u8 v_OUTPUT_SIZE = Rust_primitives.Hax.repeat 0uy v_OUTPUT_SIZE in
  let coefficient0:u8 =
    cast (v_ETA345140054 -! (simd_unit.f_coefficients.[ sz 0 ] <: i32) <: i32) <: u8
  in
  let coefficient1:u8 =
    cast (v_ETA345140054 -! (simd_unit.f_coefficients.[ sz 1 ] <: i32) <: i32) <: u8
  in
  let coefficient2:u8 =
    cast (v_ETA345140054 -! (simd_unit.f_coefficients.[ sz 2 ] <: i32) <: i32) <: u8
  in
  let coefficient3:u8 =
    cast (v_ETA345140054 -! (simd_unit.f_coefficients.[ sz 3 ] <: i32) <: i32) <: u8
  in
  let coefficient4:u8 =
    cast (v_ETA345140054 -! (simd_unit.f_coefficients.[ sz 4 ] <: i32) <: i32) <: u8
  in
  let coefficient5:u8 =
    cast (v_ETA345140054 -! (simd_unit.f_coefficients.[ sz 5 ] <: i32) <: i32) <: u8
  in
  let coefficient6:u8 =
    cast (v_ETA345140054 -! (simd_unit.f_coefficients.[ sz 6 ] <: i32) <: i32) <: u8
  in
  let coefficient7:u8 =
    cast (v_ETA345140054 -! (simd_unit.f_coefficients.[ sz 7 ] <: i32) <: i32) <: u8
  in
  let serialized:t_Array u8 v_OUTPUT_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 0)
      (((coefficient2 <<! 6l <: u8) |. (coefficient1 <<! 3l <: u8) <: u8) |. coefficient0 <: u8)
  in
  let serialized:t_Array u8 v_OUTPUT_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 1)
      ((((coefficient5 <<! 7l <: u8) |. (coefficient4 <<! 4l <: u8) <: u8) |.
          (coefficient3 <<! 1l <: u8)
          <:
          u8) |.
        (coefficient2 >>! 2l <: u8)
        <:
        u8)
  in
  let serialized:t_Array u8 v_OUTPUT_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 2)
      (((coefficient7 <<! 5l <: u8) |. (coefficient6 <<! 2l <: u8) <: u8) |.
        (coefficient5 >>! 1l <: u8)
        <:
        u8)
  in
  serialized

let serialize977980603 (simd_unit: t_PortableSIMDUnit) : t_Array u8 (sz 13) =
  let serialized:t_Array u8 (sz 13) = Rust_primitives.Hax.repeat 0uy (sz 13) in
  let coefficient0:i32 = change_t0_interval (simd_unit.f_coefficients.[ sz 0 ] <: i32) in
  let coefficient1:i32 = change_t0_interval (simd_unit.f_coefficients.[ sz 1 ] <: i32) in
  let coefficient2:i32 = change_t0_interval (simd_unit.f_coefficients.[ sz 2 ] <: i32) in
  let coefficient3:i32 = change_t0_interval (simd_unit.f_coefficients.[ sz 3 ] <: i32) in
  let coefficient4:i32 = change_t0_interval (simd_unit.f_coefficients.[ sz 4 ] <: i32) in
  let coefficient5:i32 = change_t0_interval (simd_unit.f_coefficients.[ sz 5 ] <: i32) in
  let coefficient6:i32 = change_t0_interval (simd_unit.f_coefficients.[ sz 6 ] <: i32) in
  let coefficient7:i32 = change_t0_interval (simd_unit.f_coefficients.[ sz 7 ] <: i32) in
  let serialized:t_Array u8 (sz 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 0)
      (cast (coefficient0 <: i32) <: u8)
  in
  let serialized:t_Array u8 (sz 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 1)
      (cast (coefficient0 >>! 8l <: i32) <: u8)
  in
  let serialized:t_Array u8 (sz 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 1)
      ((serialized.[ sz 1 ] <: u8) |. (cast (coefficient1 <<! 5l <: i32) <: u8) <: u8)
  in
  let serialized:t_Array u8 (sz 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 2)
      (cast (coefficient1 >>! 3l <: i32) <: u8)
  in
  let serialized:t_Array u8 (sz 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 3)
      (cast (coefficient1 >>! 11l <: i32) <: u8)
  in
  let serialized:t_Array u8 (sz 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 3)
      ((serialized.[ sz 3 ] <: u8) |. (cast (coefficient2 <<! 2l <: i32) <: u8) <: u8)
  in
  let serialized:t_Array u8 (sz 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 4)
      (cast (coefficient2 >>! 6l <: i32) <: u8)
  in
  let serialized:t_Array u8 (sz 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 4)
      ((serialized.[ sz 4 ] <: u8) |. (cast (coefficient3 <<! 7l <: i32) <: u8) <: u8)
  in
  let serialized:t_Array u8 (sz 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 5)
      (cast (coefficient3 >>! 1l <: i32) <: u8)
  in
  let serialized:t_Array u8 (sz 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 6)
      (cast (coefficient3 >>! 9l <: i32) <: u8)
  in
  let serialized:t_Array u8 (sz 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 6)
      ((serialized.[ sz 6 ] <: u8) |. (cast (coefficient4 <<! 4l <: i32) <: u8) <: u8)
  in
  let serialized:t_Array u8 (sz 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 7)
      (cast (coefficient4 >>! 4l <: i32) <: u8)
  in
  let serialized:t_Array u8 (sz 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 8)
      (cast (coefficient4 >>! 12l <: i32) <: u8)
  in
  let serialized:t_Array u8 (sz 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 8)
      ((serialized.[ sz 8 ] <: u8) |. (cast (coefficient5 <<! 1l <: i32) <: u8) <: u8)
  in
  let serialized:t_Array u8 (sz 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 9)
      (cast (coefficient5 >>! 7l <: i32) <: u8)
  in
  let serialized:t_Array u8 (sz 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 9)
      ((serialized.[ sz 9 ] <: u8) |. (cast (coefficient6 <<! 6l <: i32) <: u8) <: u8)
  in
  let serialized:t_Array u8 (sz 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 10)
      (cast (coefficient6 >>! 2l <: i32) <: u8)
  in
  let serialized:t_Array u8 (sz 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 11)
      (cast (coefficient6 >>! 10l <: i32) <: u8)
  in
  let serialized:t_Array u8 (sz 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 11)
      ((serialized.[ sz 11 ] <: u8) |. (cast (coefficient7 <<! 3l <: i32) <: u8) <: u8)
  in
  let serialized:t_Array u8 (sz 13) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
      (sz 12)
      (cast (coefficient7 >>! 5l <: i32) <: u8)
  in
  serialized

let montgomery_multiply_by_constant (simd_unit: t_PortableSIMDUnit) (c: i32) : t_PortableSIMDUnit =
  let simd_unit:t_PortableSIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32 (simd_unit.f_coefficients <: t_Slice i32) <: usize)
      (fun simd_unit temp_1_ ->
          let simd_unit:t_PortableSIMDUnit = simd_unit in
          let _:usize = temp_1_ in
          true)
      simd_unit
      (fun simd_unit i ->
          let simd_unit:t_PortableSIMDUnit = simd_unit in
          let i:usize = i in
          {
            simd_unit with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
              i
              (montgomery_reduce_element ((cast (simd_unit.f_coefficients.[ i ] <: i32) <: i64) *!
                    (cast (c <: i32) <: i64)
                    <:
                    i64)
                <:
                i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_PortableSIMDUnit)
  in
  simd_unit

let serialize1014427529 (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit)
    : t_Array u8 v_OUTPUT_SIZE =
  let serialized:t_Array u8 v_OUTPUT_SIZE = Rust_primitives.Hax.repeat 0uy v_OUTPUT_SIZE in
  match cast (v_OUTPUT_SIZE <: usize) <: u8 with
  | 4uy ->
    let serialized:t_Array u8 v_OUTPUT_SIZE =
      Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 2)
        (simd_unit.f_coefficients <: t_Slice i32)
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
        (simd_unit.f_coefficients <: t_Slice i32)
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

let serialize_when_eta_is_4_ (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit)
    : t_Array u8 v_OUTPUT_SIZE =
  let serialized:t_Array u8 v_OUTPUT_SIZE = Rust_primitives.Hax.repeat 0uy v_OUTPUT_SIZE in
  let serialized:t_Array u8 v_OUTPUT_SIZE =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 2)
      (simd_unit.f_coefficients <: t_Slice i32)
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUTPUT_SIZE = serialized in
          let _:usize = temp_1_ in
          true)
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUTPUT_SIZE = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let coefficient0:u8 =
            cast (v_ETA858068178 -! (coefficients.[ sz 0 ] <: i32) <: i32) <: u8
          in
          let coefficient1:u8 =
            cast (v_ETA858068178 -! (coefficients.[ sz 1 ] <: i32) <: i32) <: u8
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              i
              ((coefficient1 <<! 4l <: u8) |. coefficient0 <: u8)
          in
          serialized)
  in
  serialized

let serialize1006998023 (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit)
    : t_Array u8 v_OUTPUT_SIZE =
  match cast (v_OUTPUT_SIZE <: usize) <: u8 with
  | 3uy -> serialize_when_eta_is_2_ v_OUTPUT_SIZE simd_unit
  | 4uy -> serialize_when_eta_is_4_ v_OUTPUT_SIZE simd_unit
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let serialize_when_gamma1_is_2_pow_17_ (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit)
    : t_Array u8 v_OUTPUT_SIZE =
  let serialized:t_Array u8 v_OUTPUT_SIZE = Rust_primitives.Hax.repeat 0uy v_OUTPUT_SIZE in
  let serialized:t_Array u8 v_OUTPUT_SIZE =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 4)
      (simd_unit.f_coefficients <: t_Slice i32)
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUTPUT_SIZE = serialized in
          let _:usize = temp_1_ in
          true)
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUTPUT_SIZE = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let coefficient0:i32 = v_GAMMA1331343739 -! (coefficients.[ sz 0 ] <: i32) in
          let coefficient1:i32 = v_GAMMA1331343739 -! (coefficients.[ sz 1 ] <: i32) in
          let coefficient2:i32 = v_GAMMA1331343739 -! (coefficients.[ sz 2 ] <: i32) in
          let coefficient3:i32 = v_GAMMA1331343739 -! (coefficients.[ sz 3 ] <: i32) in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (sz 9 *! i <: usize)
              (cast (coefficient0 <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 1 <: usize)
              (cast (coefficient0 >>! 8l <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 2 <: usize)
              (cast (coefficient0 >>! 16l <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 2 <: usize)
              ((serialized.[ (sz 9 *! i <: usize) +! sz 2 <: usize ] <: u8) |.
                (cast (coefficient1 <<! 2l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 3 <: usize)
              (cast (coefficient1 >>! 6l <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 4 <: usize)
              (cast (coefficient1 >>! 14l <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 4 <: usize)
              ((serialized.[ (sz 9 *! i <: usize) +! sz 4 <: usize ] <: u8) |.
                (cast (coefficient2 <<! 4l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 5 <: usize)
              (cast (coefficient2 >>! 4l <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 6 <: usize)
              (cast (coefficient2 >>! 12l <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 6 <: usize)
              ((serialized.[ (sz 9 *! i <: usize) +! sz 6 <: usize ] <: u8) |.
                (cast (coefficient3 <<! 6l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 7 <: usize)
              (cast (coefficient3 >>! 2l <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 9 *! i <: usize) +! sz 8 <: usize)
              (cast (coefficient3 >>! 10l <: i32) <: u8)
          in
          serialized)
  in
  serialized

let serialize_when_gamma1_is_2_pow_19_ (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit)
    : t_Array u8 v_OUTPUT_SIZE =
  let serialized:t_Array u8 v_OUTPUT_SIZE = Rust_primitives.Hax.repeat 0uy v_OUTPUT_SIZE in
  let serialized:t_Array u8 v_OUTPUT_SIZE =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 2)
      (simd_unit.f_coefficients <: t_Slice i32)
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUTPUT_SIZE = serialized in
          let _:usize = temp_1_ in
          true)
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUTPUT_SIZE = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let coefficient0:i32 = v_GAMMA1658756807 -! (coefficients.[ sz 0 ] <: i32) in
          let coefficient1:i32 = v_GAMMA1658756807 -! (coefficients.[ sz 1 ] <: i32) in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (sz 5 *! i <: usize)
              (cast (coefficient0 <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 1 <: usize)
              (cast (coefficient0 >>! 8l <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 2 <: usize)
              (cast (coefficient0 >>! 16l <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 2 <: usize)
              ((serialized.[ (sz 5 *! i <: usize) +! sz 2 <: usize ] <: u8) |.
                (cast (coefficient1 <<! 4l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 3 <: usize)
              (cast (coefficient1 >>! 4l <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 4 <: usize)
              (cast (coefficient1 >>! 12l <: i32) <: u8)
          in
          serialized)
  in
  serialized

let serialize526929060 (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit)
    : t_Array u8 v_OUTPUT_SIZE =
  match cast (v_OUTPUT_SIZE <: usize) <: u8 with
  | 18uy -> serialize_when_gamma1_is_2_pow_17_ v_OUTPUT_SIZE simd_unit
  | 20uy -> serialize_when_gamma1_is_2_pow_19_ v_OUTPUT_SIZE simd_unit
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let serialize300254843 (simd_unit: t_PortableSIMDUnit) : t_Array u8 (sz 10) =
  let serialized:t_Array u8 (sz 10) = Rust_primitives.Hax.repeat 0uy (sz 10) in
  let serialized:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 4)
      (simd_unit.f_coefficients <: t_Slice i32)
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 (sz 10) = serialized in
          let _:usize = temp_1_ in
          true)
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 (sz 10) = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let serialized:t_Array u8 (sz 10) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (sz 5 *! i <: usize)
              (cast ((coefficients.[ sz 0 ] <: i32) &. 255l <: i32) <: u8)
          in
          let serialized:t_Array u8 (sz 10) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 1 <: usize)
              (((cast ((coefficients.[ sz 1 ] <: i32) &. 63l <: i32) <: u8) <<! 2l <: u8) |.
                (cast (((coefficients.[ sz 0 ] <: i32) >>! 8l <: i32) &. 3l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 (sz 10) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 2 <: usize)
              (((cast ((coefficients.[ sz 2 ] <: i32) &. 15l <: i32) <: u8) <<! 4l <: u8) |.
                (cast (((coefficients.[ sz 1 ] <: i32) >>! 6l <: i32) &. 15l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 (sz 10) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 3 <: usize)
              (((cast ((coefficients.[ sz 3 ] <: i32) &. 3l <: i32) <: u8) <<! 6l <: u8) |.
                (cast (((coefficients.[ sz 2 ] <: i32) >>! 4l <: i32) &. 63l <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 (sz 10) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((sz 5 *! i <: usize) +! sz 4 <: usize)
              (cast (((coefficients.[ sz 3 ] <: i32) >>! 2l <: i32) &. 255l <: i32) <: u8)
          in
          serialized)
  in
  serialized

let ntt_at_layer_0_ (zeta_i: usize) (re: t_Array t_PortableSIMDUnit (sz 32))
    : (usize & t_Array t_PortableSIMDUnit (sz 32)) =
  let zeta_i:usize = zeta_i +! sz 1 in
  let re, zeta_i:(t_Array t_PortableSIMDUnit (sz 32) & usize) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #t_PortableSIMDUnit (re <: t_Slice t_PortableSIMDUnit) <: usize)
      (fun temp_0_ temp_1_ ->
          let re, zeta_i:(t_Array t_PortableSIMDUnit (sz 32) & usize) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (re, zeta_i <: (t_Array t_PortableSIMDUnit (sz 32) & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_Array t_PortableSIMDUnit (sz 32) & usize) = temp_0_ in
          let round:usize = round in
          let re:t_Array t_PortableSIMDUnit (sz 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              round
              (simd_unit_ntt_at_layer_0_ (re.[ round ] <: t_PortableSIMDUnit)
                  (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                  (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +! sz 1 <: usize ]
                    <:
                    i32)
                  (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +! sz 2 <: usize ]
                    <:
                    i32)
                  (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +! sz 3 <: usize ]
                    <:
                    i32)
                <:
                t_PortableSIMDUnit)
          in
          let zeta_i:usize = zeta_i +! sz 4 in
          re, zeta_i <: (t_Array t_PortableSIMDUnit (sz 32) & usize))
  in
  let zeta_i:usize = zeta_i -! sz 1 in
  zeta_i, re <: (usize & t_Array t_PortableSIMDUnit (sz 32))

let ntt_at_layer_1_ (zeta_i: usize) (re: t_Array t_PortableSIMDUnit (sz 32))
    : (usize & t_Array t_PortableSIMDUnit (sz 32)) =
  let zeta_i:usize = zeta_i +! sz 1 in
  let re, zeta_i:(t_Array t_PortableSIMDUnit (sz 32) & usize) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #t_PortableSIMDUnit (re <: t_Slice t_PortableSIMDUnit) <: usize)
      (fun temp_0_ temp_1_ ->
          let re, zeta_i:(t_Array t_PortableSIMDUnit (sz 32) & usize) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (re, zeta_i <: (t_Array t_PortableSIMDUnit (sz 32) & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_Array t_PortableSIMDUnit (sz 32) & usize) = temp_0_ in
          let round:usize = round in
          let re:t_Array t_PortableSIMDUnit (sz 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              round
              (simd_unit_ntt_at_layer_1_ (re.[ round ] <: t_PortableSIMDUnit)
                  (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                  (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i +! sz 1 <: usize ]
                    <:
                    i32)
                <:
                t_PortableSIMDUnit)
          in
          let zeta_i:usize = zeta_i +! sz 2 in
          re, zeta_i <: (t_Array t_PortableSIMDUnit (sz 32) & usize))
  in
  let zeta_i:usize = zeta_i -! sz 1 in
  zeta_i, re <: (usize & t_Array t_PortableSIMDUnit (sz 32))

let ntt_at_layer_2_ (zeta_i: usize) (re: t_Array t_PortableSIMDUnit (sz 32))
    : (usize & t_Array t_PortableSIMDUnit (sz 32)) =
  let (re, zeta_i), hax_temp_output:((t_Array t_PortableSIMDUnit (sz 32) & usize) & Prims.unit) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #t_PortableSIMDUnit (re <: t_Slice t_PortableSIMDUnit) <: usize)
      (fun temp_0_ temp_1_ ->
          let re, zeta_i:(t_Array t_PortableSIMDUnit (sz 32) & usize) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (re, zeta_i <: (t_Array t_PortableSIMDUnit (sz 32) & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_Array t_PortableSIMDUnit (sz 32) & usize) = temp_0_ in
          let round:usize = round in
          let zeta_i:usize = zeta_i +! sz 1 in
          let re:t_Array t_PortableSIMDUnit (sz 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              round
              (simd_unit_ntt_at_layer_2_ (re.[ round ] <: t_PortableSIMDUnit)
                  (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                <:
                t_PortableSIMDUnit)
          in
          re, zeta_i <: (t_Array t_PortableSIMDUnit (sz 32) & usize))
  in
  zeta_i, re <: (usize & t_Array t_PortableSIMDUnit (sz 32))

let rec add (lhs rhs: t_PortableSIMDUnit) : t_PortableSIMDUnit =
  let sum:t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #t_PortableSIMDUnit #FStar.Tactics.Typeclasses.solve ()
  in
  let sum:t_PortableSIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32 (sum.f_coefficients <: t_Slice i32) <: usize)
      (fun sum temp_1_ ->
          let sum:t_PortableSIMDUnit = sum in
          let _:usize = temp_1_ in
          true)
      sum
      (fun sum i ->
          let sum:t_PortableSIMDUnit = sum in
          let i:usize = i in
          {
            sum with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize sum.f_coefficients
              i
              ((lhs.f_coefficients.[ i ] <: i32) +! (rhs.f_coefficients.[ i ] <: i32) <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_PortableSIMDUnit)
  in
  sum

and compute_hint (v_GAMMA2: i32) (low high: t_PortableSIMDUnit) : (usize & t_PortableSIMDUnit) =
  let hint:t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #t_PortableSIMDUnit #FStar.Tactics.Typeclasses.solve ()
  in
  let one_hints_count:usize = sz 0 in
  let hint, one_hints_count:(t_PortableSIMDUnit & usize) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32 (hint.f_coefficients <: t_Slice i32) <: usize)
      (fun temp_0_ temp_1_ ->
          let hint, one_hints_count:(t_PortableSIMDUnit & usize) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (hint, one_hints_count <: (t_PortableSIMDUnit & usize))
      (fun temp_0_ i ->
          let hint, one_hints_count:(t_PortableSIMDUnit & usize) = temp_0_ in
          let i:usize = i in
          let hint:t_PortableSIMDUnit =
            {
              hint with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hint.f_coefficients
                i
                (compute_one_hint v_GAMMA2
                    (low.f_coefficients.[ i ] <: i32)
                    (high.f_coefficients.[ i ] <: i32)
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let one_hints_count:usize =
            one_hints_count +! (cast (hint.f_coefficients.[ i ] <: i32) <: usize)
          in
          hint, one_hints_count <: (t_PortableSIMDUnit & usize))
  in
  one_hints_count, hint <: (usize & t_PortableSIMDUnit)

and decompose (v_GAMMA2: i32) (simd_unit: t_PortableSIMDUnit)
    : (t_PortableSIMDUnit & t_PortableSIMDUnit) =
  let low:t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #t_PortableSIMDUnit #FStar.Tactics.Typeclasses.solve ()
  in
  let high:t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #t_PortableSIMDUnit #FStar.Tactics.Typeclasses.solve ()
  in
  let high, low:(t_PortableSIMDUnit & t_PortableSIMDUnit) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32 (low.f_coefficients <: t_Slice i32) <: usize)
      (fun temp_0_ temp_1_ ->
          let high, low:(t_PortableSIMDUnit & t_PortableSIMDUnit) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (high, low <: (t_PortableSIMDUnit & t_PortableSIMDUnit))
      (fun temp_0_ i ->
          let high, low:(t_PortableSIMDUnit & t_PortableSIMDUnit) = temp_0_ in
          let i:usize = i in
          let low_part, high_part:(i32 & i32) =
            decompose_element v_GAMMA2 (simd_unit.f_coefficients.[ i ] <: i32)
          in
          let low:t_PortableSIMDUnit =
            {
              low with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low.f_coefficients
                i
                low_part
            }
            <:
            t_PortableSIMDUnit
          in
          let high:t_PortableSIMDUnit =
            {
              high with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high.f_coefficients
                i
                high_part
            }
            <:
            t_PortableSIMDUnit
          in
          high, low <: (t_PortableSIMDUnit & t_PortableSIMDUnit))
  in
  low, high <: (t_PortableSIMDUnit & t_PortableSIMDUnit)

and montgomery_multiply (lhs rhs: t_PortableSIMDUnit) : t_PortableSIMDUnit =
  let product:t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #t_PortableSIMDUnit #FStar.Tactics.Typeclasses.solve ()
  in
  let product:t_PortableSIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32 (product.f_coefficients <: t_Slice i32) <: usize)
      (fun product temp_1_ ->
          let product:t_PortableSIMDUnit = product in
          let _:usize = temp_1_ in
          true)
      product
      (fun product i ->
          let product:t_PortableSIMDUnit = product in
          let i:usize = i in
          {
            product with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize product.f_coefficients
              i
              (montgomery_reduce_element ((cast (lhs.f_coefficients.[ i ] <: i32) <: i64) *!
                    (cast (rhs.f_coefficients.[ i ] <: i32) <: i64)
                    <:
                    i64)
                <:
                i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_PortableSIMDUnit)
  in
  product

and power2round (simd_unit: t_PortableSIMDUnit) : (t_PortableSIMDUnit & t_PortableSIMDUnit) =
  let t0_simd_unit:t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #t_PortableSIMDUnit #FStar.Tactics.Typeclasses.solve ()
  in
  let t1_simd_unit:t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #t_PortableSIMDUnit #FStar.Tactics.Typeclasses.solve ()
  in
  let t0_simd_unit, t1_simd_unit:(t_PortableSIMDUnit & t_PortableSIMDUnit) =
    Rust_primitives.Hax.Folds.fold_enumerated_slice simd_unit.f_coefficients
      (fun temp_0_ temp_1_ ->
          let t0_simd_unit, t1_simd_unit:(t_PortableSIMDUnit & t_PortableSIMDUnit) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (t0_simd_unit, t1_simd_unit <: (t_PortableSIMDUnit & t_PortableSIMDUnit))
      (fun temp_0_ temp_1_ ->
          let t0_simd_unit, t1_simd_unit:(t_PortableSIMDUnit & t_PortableSIMDUnit) = temp_0_ in
          let i, t:(usize & i32) = temp_1_ in
          let t0, t1:(i32 & i32) = power2round_element t in
          let t0_simd_unit:t_PortableSIMDUnit =
            {
              t0_simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize t0_simd_unit
                  .f_coefficients
                i
                t0
            }
            <:
            t_PortableSIMDUnit
          in
          let t1_simd_unit:t_PortableSIMDUnit =
            {
              t1_simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize t1_simd_unit
                  .f_coefficients
                i
                t1
            }
            <:
            t_PortableSIMDUnit
          in
          t0_simd_unit, t1_simd_unit <: (t_PortableSIMDUnit & t_PortableSIMDUnit))
  in
  t0_simd_unit, t1_simd_unit <: (t_PortableSIMDUnit & t_PortableSIMDUnit)

and shift_left_then_reduce (v_SHIFT_BY: i32) (simd_unit: t_PortableSIMDUnit) : t_PortableSIMDUnit =
  let out:t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #t_PortableSIMDUnit #FStar.Tactics.Typeclasses.solve ()
  in
  let out:t_PortableSIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32 (simd_unit.f_coefficients <: t_Slice i32) <: usize)
      (fun out temp_1_ ->
          let out:t_PortableSIMDUnit = out in
          let _:usize = temp_1_ in
          true)
      out
      (fun out i ->
          let out:t_PortableSIMDUnit = out in
          let i:usize = i in
          {
            out with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_coefficients
              i
              (reduce_element ((simd_unit.f_coefficients.[ i ] <: i32) <<! v_SHIFT_BY <: i32) <: i32
              )
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_PortableSIMDUnit)
  in
  out

and subtract (lhs rhs: t_PortableSIMDUnit) : t_PortableSIMDUnit =
  let difference:t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #t_PortableSIMDUnit #FStar.Tactics.Typeclasses.solve ()
  in
  let difference:t_PortableSIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32 (difference.f_coefficients <: t_Slice i32) <: usize)
      (fun difference temp_1_ ->
          let difference:t_PortableSIMDUnit = difference in
          let _:usize = temp_1_ in
          true)
      difference
      (fun difference i ->
          let difference:t_PortableSIMDUnit = difference in
          let i:usize = i in
          {
            difference with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize difference.f_coefficients
              i
              ((lhs.f_coefficients.[ i ] <: i32) -! (rhs.f_coefficients.[ i ] <: i32) <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_PortableSIMDUnit)
  in
  difference

and use_hint (v_GAMMA2: i32) (simd_unit hint: t_PortableSIMDUnit) : t_PortableSIMDUnit =
  let result:t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #t_PortableSIMDUnit #FStar.Tactics.Typeclasses.solve ()
  in
  let result:t_PortableSIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32 (result.f_coefficients <: t_Slice i32) <: usize)
      (fun result temp_1_ ->
          let result:t_PortableSIMDUnit = result in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:t_PortableSIMDUnit = result in
          let i:usize = i in
          {
            result with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_coefficients
              i
              (use_one_hint v_GAMMA2
                  (simd_unit.f_coefficients.[ i ] <: i32)
                  (hint.f_coefficients.[ i ] <: i32)
                <:
                i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_PortableSIMDUnit)
  in
  result

and deserialize_when_eta_is_2_ (serialized: t_Slice u8) : t_PortableSIMDUnit =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. sz 3 <: bool)
      in
      ()
  in
  let simd_unit:t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #t_PortableSIMDUnit #FStar.Tactics.Typeclasses.solve ()
  in
  let byte0:i32 = cast (serialized.[ sz 0 ] <: u8) <: i32 in
  let byte1:i32 = cast (serialized.[ sz 1 ] <: u8) <: i32 in
  let byte2:i32 = cast (serialized.[ sz 2 ] <: u8) <: i32 in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 0)
        (v_ETA832233724 -! (byte0 &. 7l <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 1)
        (v_ETA832233724 -! ((byte0 >>! 3l <: i32) &. 7l <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 2)
        (v_ETA832233724 -! (((byte0 >>! 6l <: i32) |. (byte1 <<! 2l <: i32) <: i32) &. 7l <: i32)
          <:
          i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 3)
        (v_ETA832233724 -! ((byte1 >>! 1l <: i32) &. 7l <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 4)
        (v_ETA832233724 -! ((byte1 >>! 4l <: i32) &. 7l <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 5)
        (v_ETA832233724 -! (((byte1 >>! 7l <: i32) |. (byte2 <<! 1l <: i32) <: i32) &. 7l <: i32)
          <:
          i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 6)
        (v_ETA832233724 -! ((byte2 >>! 2l <: i32) &. 7l <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 7)
        (v_ETA832233724 -! ((byte2 >>! 5l <: i32) &. 7l <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  simd_unit

and deserialize_when_eta_is_4_ (serialized: t_Slice u8) : t_PortableSIMDUnit =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. sz 4 <: bool)
      in
      ()
  in
  let simd_unit:t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #t_PortableSIMDUnit #FStar.Tactics.Typeclasses.solve ()
  in
  let simd_unit:t_PortableSIMDUnit =
    Rust_primitives.Hax.Folds.fold_enumerated_slice serialized
      (fun simd_unit temp_1_ ->
          let simd_unit:t_PortableSIMDUnit = simd_unit in
          let _:usize = temp_1_ in
          true)
      simd_unit
      (fun simd_unit temp_1_ ->
          let simd_unit:t_PortableSIMDUnit = simd_unit in
          let i, byte:(usize & u8) = temp_1_ in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                (sz 2 *! i <: usize)
                (v_ETA177254429 -! (cast (byte &. 15uy <: u8) <: i32) <: i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 2 *! i <: usize) +! sz 1 <: usize)
                (v_ETA177254429 -! (cast (byte >>! 4l <: u8) <: i32) <: i32)
            }
            <:
            t_PortableSIMDUnit
          in
          simd_unit)
  in
  simd_unit

and deserialize154437703 (v_ETA: usize) (serialized: t_Slice u8) : t_PortableSIMDUnit =
  match cast (v_ETA <: usize) <: u8 with
  | 2uy -> deserialize_when_eta_is_2_ serialized
  | 4uy -> deserialize_when_eta_is_4_ serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

and deserialize_when_gamma1_is_2_pow_17_ (serialized: t_Slice u8) : t_PortableSIMDUnit =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. sz 18 <: bool)
      in
      ()
  in
  let simd_unit:t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #t_PortableSIMDUnit #FStar.Tactics.Typeclasses.solve ()
  in
  let simd_unit:t_PortableSIMDUnit =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 9)
      serialized
      (fun simd_unit temp_1_ ->
          let simd_unit:t_PortableSIMDUnit = simd_unit in
          let _:usize = temp_1_ in
          true)
      simd_unit
      (fun simd_unit temp_1_ ->
          let simd_unit:t_PortableSIMDUnit = simd_unit in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                (sz 4 *! i <: usize)
                (cast (bytes.[ sz 0 ] <: u8) <: i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                (sz 4 *! i <: usize)
                ((simd_unit.f_coefficients.[ sz 4 *! i <: usize ] <: i32) |.
                  ((cast (bytes.[ sz 1 ] <: u8) <: i32) <<! 8l <: i32)
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                (sz 4 *! i <: usize)
                ((simd_unit.f_coefficients.[ sz 4 *! i <: usize ] <: i32) |.
                  ((cast (bytes.[ sz 2 ] <: u8) <: i32) <<! 16l <: i32)
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                (sz 4 *! i <: usize)
                ((simd_unit.f_coefficients.[ sz 4 *! i <: usize ] <: i32) &.
                  v_GAMMA1_TIMES_2_BITMASK305664693
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 4 *! i <: usize) +! sz 1 <: usize)
                ((cast (bytes.[ sz 2 ] <: u8) <: i32) >>! 2l <: i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 4 *! i <: usize) +! sz 1 <: usize)
                ((simd_unit.f_coefficients.[ (sz 4 *! i <: usize) +! sz 1 <: usize ] <: i32) |.
                  ((cast (bytes.[ sz 3 ] <: u8) <: i32) <<! 6l <: i32)
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 4 *! i <: usize) +! sz 1 <: usize)
                ((simd_unit.f_coefficients.[ (sz 4 *! i <: usize) +! sz 1 <: usize ] <: i32) |.
                  ((cast (bytes.[ sz 4 ] <: u8) <: i32) <<! 14l <: i32)
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 4 *! i <: usize) +! sz 1 <: usize)
                ((simd_unit.f_coefficients.[ (sz 4 *! i <: usize) +! sz 1 <: usize ] <: i32) &.
                  v_GAMMA1_TIMES_2_BITMASK305664693
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 4 *! i <: usize) +! sz 2 <: usize)
                ((cast (bytes.[ sz 4 ] <: u8) <: i32) >>! 4l <: i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 4 *! i <: usize) +! sz 2 <: usize)
                ((simd_unit.f_coefficients.[ (sz 4 *! i <: usize) +! sz 2 <: usize ] <: i32) |.
                  ((cast (bytes.[ sz 5 ] <: u8) <: i32) <<! 4l <: i32)
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 4 *! i <: usize) +! sz 2 <: usize)
                ((simd_unit.f_coefficients.[ (sz 4 *! i <: usize) +! sz 2 <: usize ] <: i32) |.
                  ((cast (bytes.[ sz 6 ] <: u8) <: i32) <<! 12l <: i32)
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 4 *! i <: usize) +! sz 2 <: usize)
                ((simd_unit.f_coefficients.[ (sz 4 *! i <: usize) +! sz 2 <: usize ] <: i32) &.
                  v_GAMMA1_TIMES_2_BITMASK305664693
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 4 *! i <: usize) +! sz 3 <: usize)
                ((cast (bytes.[ sz 6 ] <: u8) <: i32) >>! 6l <: i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 4 *! i <: usize) +! sz 3 <: usize)
                ((simd_unit.f_coefficients.[ (sz 4 *! i <: usize) +! sz 3 <: usize ] <: i32) |.
                  ((cast (bytes.[ sz 7 ] <: u8) <: i32) <<! 2l <: i32)
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 4 *! i <: usize) +! sz 3 <: usize)
                ((simd_unit.f_coefficients.[ (sz 4 *! i <: usize) +! sz 3 <: usize ] <: i32) |.
                  ((cast (bytes.[ sz 8 ] <: u8) <: i32) <<! 10l <: i32)
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 4 *! i <: usize) +! sz 3 <: usize)
                ((simd_unit.f_coefficients.[ (sz 4 *! i <: usize) +! sz 3 <: usize ] <: i32) &.
                  v_GAMMA1_TIMES_2_BITMASK305664693
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                (sz 4 *! i <: usize)
                (v_GAMMA1183990813 -! (simd_unit.f_coefficients.[ sz 4 *! i <: usize ] <: i32)
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 4 *! i <: usize) +! sz 1 <: usize)
                (v_GAMMA1183990813 -!
                  (simd_unit.f_coefficients.[ (sz 4 *! i <: usize) +! sz 1 <: usize ] <: i32)
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 4 *! i <: usize) +! sz 2 <: usize)
                (v_GAMMA1183990813 -!
                  (simd_unit.f_coefficients.[ (sz 4 *! i <: usize) +! sz 2 <: usize ] <: i32)
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 4 *! i <: usize) +! sz 3 <: usize)
                (v_GAMMA1183990813 -!
                  (simd_unit.f_coefficients.[ (sz 4 *! i <: usize) +! sz 3 <: usize ] <: i32)
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          simd_unit)
  in
  simd_unit

and deserialize_when_gamma1_is_2_pow_19_ (serialized: t_Slice u8) : t_PortableSIMDUnit =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. sz 20 <: bool)
      in
      ()
  in
  let simd_unit:t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #t_PortableSIMDUnit #FStar.Tactics.Typeclasses.solve ()
  in
  let simd_unit:t_PortableSIMDUnit =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 5)
      serialized
      (fun simd_unit temp_1_ ->
          let simd_unit:t_PortableSIMDUnit = simd_unit in
          let _:usize = temp_1_ in
          true)
      simd_unit
      (fun simd_unit temp_1_ ->
          let simd_unit:t_PortableSIMDUnit = simd_unit in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                (sz 2 *! i <: usize)
                (cast (bytes.[ sz 0 ] <: u8) <: i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                (sz 2 *! i <: usize)
                ((simd_unit.f_coefficients.[ sz 2 *! i <: usize ] <: i32) |.
                  ((cast (bytes.[ sz 1 ] <: u8) <: i32) <<! 8l <: i32)
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                (sz 2 *! i <: usize)
                ((simd_unit.f_coefficients.[ sz 2 *! i <: usize ] <: i32) |.
                  ((cast (bytes.[ sz 2 ] <: u8) <: i32) <<! 16l <: i32)
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                (sz 2 *! i <: usize)
                ((simd_unit.f_coefficients.[ sz 2 *! i <: usize ] <: i32) &.
                  v_GAMMA1_TIMES_2_BITMASK614047129
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 2 *! i <: usize) +! sz 1 <: usize)
                ((cast (bytes.[ sz 2 ] <: u8) <: i32) >>! 4l <: i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 2 *! i <: usize) +! sz 1 <: usize)
                ((simd_unit.f_coefficients.[ (sz 2 *! i <: usize) +! sz 1 <: usize ] <: i32) |.
                  ((cast (bytes.[ sz 3 ] <: u8) <: i32) <<! 4l <: i32)
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 2 *! i <: usize) +! sz 1 <: usize)
                ((simd_unit.f_coefficients.[ (sz 2 *! i <: usize) +! sz 1 <: usize ] <: i32) |.
                  ((cast (bytes.[ sz 4 ] <: u8) <: i32) <<! 12l <: i32)
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                (sz 2 *! i <: usize)
                (v_GAMMA1465203885 -! (simd_unit.f_coefficients.[ sz 2 *! i <: usize ] <: i32)
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 2 *! i <: usize) +! sz 1 <: usize)
                (v_GAMMA1465203885 -!
                  (simd_unit.f_coefficients.[ (sz 2 *! i <: usize) +! sz 1 <: usize ] <: i32)
                  <:
                  i32)
            }
            <:
            t_PortableSIMDUnit
          in
          simd_unit)
  in
  simd_unit

and deserialize244287932 (v_GAMMA1_EXPONENT: usize) (serialized: t_Slice u8) : t_PortableSIMDUnit =
  match cast (v_GAMMA1_EXPONENT <: usize) <: u8 with
  | 17uy -> deserialize_when_gamma1_is_2_pow_17_ serialized
  | 19uy -> deserialize_when_gamma1_is_2_pow_19_ serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

and deserialize297775919 (serialized: t_Slice u8) : t_PortableSIMDUnit =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. sz 13 <: bool)
      in
      ()
  in
  let simd_unit:t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #t_PortableSIMDUnit #FStar.Tactics.Typeclasses.solve ()
  in
  let byte0:i32 = cast (serialized.[ sz 0 ] <: u8) <: i32 in
  let byte1:i32 = cast (serialized.[ sz 1 ] <: u8) <: i32 in
  let byte2:i32 = cast (serialized.[ sz 2 ] <: u8) <: i32 in
  let byte3:i32 = cast (serialized.[ sz 3 ] <: u8) <: i32 in
  let byte4:i32 = cast (serialized.[ sz 4 ] <: u8) <: i32 in
  let byte5:i32 = cast (serialized.[ sz 5 ] <: u8) <: i32 in
  let byte6:i32 = cast (serialized.[ sz 6 ] <: u8) <: i32 in
  let byte7:i32 = cast (serialized.[ sz 7 ] <: u8) <: i32 in
  let byte8:i32 = cast (serialized.[ sz 8 ] <: u8) <: i32 in
  let byte9:i32 = cast (serialized.[ sz 9 ] <: u8) <: i32 in
  let byte10:i32 = cast (serialized.[ sz 10 ] <: u8) <: i32 in
  let byte11:i32 = cast (serialized.[ sz 11 ] <: u8) <: i32 in
  let byte12:i32 = cast (serialized.[ sz 12 ] <: u8) <: i32 in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 0)
        byte0
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 0)
        ((simd_unit.f_coefficients.[ sz 0 ] <: i32) |. (byte1 <<! 8l <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 0)
        ((simd_unit.f_coefficients.[ sz 0 ] <: i32) &. v_BITS_IN_LOWER_PART_OF_T_MASK <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 1)
        (byte1 >>! 5l <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 1)
        ((simd_unit.f_coefficients.[ sz 1 ] <: i32) |. (byte2 <<! 3l <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 1)
        ((simd_unit.f_coefficients.[ sz 1 ] <: i32) |. (byte3 <<! 11l <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 1)
        ((simd_unit.f_coefficients.[ sz 1 ] <: i32) &. v_BITS_IN_LOWER_PART_OF_T_MASK <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 2)
        (byte3 >>! 2l <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 2)
        ((simd_unit.f_coefficients.[ sz 2 ] <: i32) |. (byte4 <<! 6l <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 2)
        ((simd_unit.f_coefficients.[ sz 2 ] <: i32) &. v_BITS_IN_LOWER_PART_OF_T_MASK <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 3)
        (byte4 >>! 7l <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 3)
        ((simd_unit.f_coefficients.[ sz 3 ] <: i32) |. (byte5 <<! 1l <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 3)
        ((simd_unit.f_coefficients.[ sz 3 ] <: i32) |. (byte6 <<! 9l <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 3)
        ((simd_unit.f_coefficients.[ sz 3 ] <: i32) &. v_BITS_IN_LOWER_PART_OF_T_MASK <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 4)
        (byte6 >>! 4l <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 4)
        ((simd_unit.f_coefficients.[ sz 4 ] <: i32) |. (byte7 <<! 4l <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 4)
        ((simd_unit.f_coefficients.[ sz 4 ] <: i32) |. (byte8 <<! 12l <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 4)
        ((simd_unit.f_coefficients.[ sz 4 ] <: i32) &. v_BITS_IN_LOWER_PART_OF_T_MASK <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 5)
        (byte8 >>! 1l <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 5)
        ((simd_unit.f_coefficients.[ sz 5 ] <: i32) |. (byte9 <<! 7l <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 5)
        ((simd_unit.f_coefficients.[ sz 5 ] <: i32) &. v_BITS_IN_LOWER_PART_OF_T_MASK <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 6)
        (byte9 >>! 6l <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 6)
        ((simd_unit.f_coefficients.[ sz 6 ] <: i32) |. (byte10 <<! 2l <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 6)
        ((simd_unit.f_coefficients.[ sz 6 ] <: i32) |. (byte11 <<! 10l <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 6)
        ((simd_unit.f_coefficients.[ sz 6 ] <: i32) &. v_BITS_IN_LOWER_PART_OF_T_MASK <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 7)
        (byte11 >>! 3l <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 7)
        ((simd_unit.f_coefficients.[ sz 7 ] <: i32) |. (byte12 <<! 5l <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 7)
        ((simd_unit.f_coefficients.[ sz 7 ] <: i32) &. v_BITS_IN_LOWER_PART_OF_T_MASK <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 0)
        (change_t0_interval (simd_unit.f_coefficients.[ sz 0 ] <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 1)
        (change_t0_interval (simd_unit.f_coefficients.[ sz 1 ] <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 2)
        (change_t0_interval (simd_unit.f_coefficients.[ sz 2 ] <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 3)
        (change_t0_interval (simd_unit.f_coefficients.[ sz 3 ] <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 4)
        (change_t0_interval (simd_unit.f_coefficients.[ sz 4 ] <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 5)
        (change_t0_interval (simd_unit.f_coefficients.[ sz 5 ] <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 6)
        (change_t0_interval (simd_unit.f_coefficients.[ sz 6 ] <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  let simd_unit:t_PortableSIMDUnit =
    {
      simd_unit with
      f_coefficients
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
        (sz 7)
        (change_t0_interval (simd_unit.f_coefficients.[ sz 7 ] <: i32) <: i32)
    }
    <:
    t_PortableSIMDUnit
  in
  simd_unit

and deserialize960784460 (serialized: t_Slice u8) : t_PortableSIMDUnit =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. sz 10 <: bool)
      in
      ()
  in
  let simd_unit:t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #t_PortableSIMDUnit #FStar.Tactics.Typeclasses.solve ()
  in
  let mask:i32 = (1l <<! Libcrux_ml_dsa.Constants.v_BITS_IN_UPPER_PART_OF_T <: i32) -! 1l in
  let simd_unit:t_PortableSIMDUnit =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (sz 5)
      serialized
      (fun simd_unit temp_1_ ->
          let simd_unit:t_PortableSIMDUnit = simd_unit in
          let _:usize = temp_1_ in
          true)
      simd_unit
      (fun simd_unit temp_1_ ->
          let simd_unit:t_PortableSIMDUnit = simd_unit in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let byte0:i32 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
          let byte1:i32 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
          let byte2:i32 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
          let byte3:i32 = cast (bytes.[ sz 3 ] <: u8) <: i32 in
          let byte4:i32 = cast (bytes.[ sz 4 ] <: u8) <: i32 in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                (sz 4 *! i <: usize)
                ((byte0 |. (byte1 <<! 8l <: i32) <: i32) &. mask <: i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 4 *! i <: usize) +! sz 1 <: usize)
                (((byte1 >>! 2l <: i32) |. (byte2 <<! 6l <: i32) <: i32) &. mask <: i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 4 *! i <: usize) +! sz 2 <: usize)
                (((byte2 >>! 4l <: i32) |. (byte3 <<! 4l <: i32) <: i32) &. mask <: i32)
            }
            <:
            t_PortableSIMDUnit
          in
          let simd_unit:t_PortableSIMDUnit =
            {
              simd_unit with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit.f_coefficients
                ((sz 4 *! i <: usize) +! sz 3 <: usize)
                (((byte3 >>! 6l <: i32) |. (byte4 <<! 2l <: i32) <: i32) &. mask <: i32)
            }
            <:
            t_PortableSIMDUnit
          in
          simd_unit)
  in
  simd_unit

and ntt (re: t_Array t_PortableSIMDUnit (sz 32)) : t_Array t_PortableSIMDUnit (sz 32) =
  let zeta_i:usize = sz 0 in
  let tmp0, tmp1:(usize & t_Array t_PortableSIMDUnit (sz 32)) =
    ntt_at_layer_3_plus (sz 7) zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array t_PortableSIMDUnit (sz 32) = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & t_Array t_PortableSIMDUnit (sz 32)) =
    ntt_at_layer_3_plus (sz 6) zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array t_PortableSIMDUnit (sz 32) = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & t_Array t_PortableSIMDUnit (sz 32)) =
    ntt_at_layer_3_plus (sz 5) zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array t_PortableSIMDUnit (sz 32) = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & t_Array t_PortableSIMDUnit (sz 32)) =
    ntt_at_layer_3_plus (sz 4) zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array t_PortableSIMDUnit (sz 32) = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & t_Array t_PortableSIMDUnit (sz 32)) =
    ntt_at_layer_3_plus (sz 3) zeta_i re
  in
  let zeta_i:usize = tmp0 in
  let re:t_Array t_PortableSIMDUnit (sz 32) = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & t_Array t_PortableSIMDUnit (sz 32)) = ntt_at_layer_2_ zeta_i re in
  let zeta_i:usize = tmp0 in
  let re:t_Array t_PortableSIMDUnit (sz 32) = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & t_Array t_PortableSIMDUnit (sz 32)) = ntt_at_layer_1_ zeta_i re in
  let zeta_i:usize = tmp0 in
  let re:t_Array t_PortableSIMDUnit (sz 32) = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(usize & t_Array t_PortableSIMDUnit (sz 32)) = ntt_at_layer_0_ zeta_i re in
  let zeta_i:usize = tmp0 in
  let re:t_Array t_PortableSIMDUnit (sz 32) = tmp1 in
  let _:Prims.unit = () in
  re

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_ml_dsa.Simd.Traits.t_Operations t_PortableSIMDUnit =
  {
    _super_11581440318597584651 = FStar.Tactics.Typeclasses.solve;
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    f_ZERO_pre = (fun (_: Prims.unit) -> true);
    f_ZERO_post = (fun (_: Prims.unit) (out: t_PortableSIMDUnit) -> true);
    f_ZERO
    =
    (fun (_: Prims.unit) ->
        { f_coefficients = Rust_primitives.Hax.repeat 0l (sz 8) } <: t_PortableSIMDUnit);
    f_from_coefficient_array_pre = (fun (array: t_Slice i32) -> true);
    f_from_coefficient_array_post = (fun (array: t_Slice i32) (out: t_PortableSIMDUnit) -> true);
    f_from_coefficient_array
    =
    (fun (array: t_Slice i32) ->
        {
          f_coefficients
          =
          Core.Result.impl__unwrap #(t_Array i32 (sz 8))
            #Core.Array.t_TryFromSliceError
            (Core.Convert.f_try_into #(t_Slice i32)
                #(t_Array i32 (sz 8))
                #FStar.Tactics.Typeclasses.solve
                (array.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice i32)
              <:
              Core.Result.t_Result (t_Array i32 (sz 8)) Core.Array.t_TryFromSliceError)
        }
        <:
        t_PortableSIMDUnit);
    f_to_coefficient_array_pre = (fun (self: t_PortableSIMDUnit) -> true);
    f_to_coefficient_array_post = (fun (self: t_PortableSIMDUnit) (out: t_Array i32 (sz 8)) -> true);
    f_to_coefficient_array
    =
    (fun (self: t_PortableSIMDUnit) ->
        Core.Result.impl__unwrap #(t_Array i32 (sz 8))
          #Core.Convert.t_Infallible
          (Core.Convert.f_try_into #(t_Array i32 (sz 8))
              #(t_Array i32 (sz 8))
              #FStar.Tactics.Typeclasses.solve
              self.f_coefficients
            <:
            Core.Result.t_Result (t_Array i32 (sz 8)) Core.Convert.t_Infallible));
    f_add_pre = (fun (lhs: t_PortableSIMDUnit) (rhs: t_PortableSIMDUnit) -> true);
    f_add_post
    =
    (fun (lhs: t_PortableSIMDUnit) (rhs: t_PortableSIMDUnit) (out: t_PortableSIMDUnit) -> true);
    f_add = (fun (lhs: t_PortableSIMDUnit) (rhs: t_PortableSIMDUnit) -> add lhs rhs);
    f_subtract_pre = (fun (lhs: t_PortableSIMDUnit) (rhs: t_PortableSIMDUnit) -> true);
    f_subtract_post
    =
    (fun (lhs: t_PortableSIMDUnit) (rhs: t_PortableSIMDUnit) (out: t_PortableSIMDUnit) -> true);
    f_subtract = (fun (lhs: t_PortableSIMDUnit) (rhs: t_PortableSIMDUnit) -> subtract lhs rhs);
    f_montgomery_multiply_by_constant_pre = (fun (simd_unit: t_PortableSIMDUnit) (c: i32) -> true);
    f_montgomery_multiply_by_constant_post
    =
    (fun (simd_unit: t_PortableSIMDUnit) (c: i32) (out: t_PortableSIMDUnit) -> true);
    f_montgomery_multiply_by_constant
    =
    (fun (simd_unit: t_PortableSIMDUnit) (c: i32) -> montgomery_multiply_by_constant simd_unit c);
    f_montgomery_multiply_pre = (fun (lhs: t_PortableSIMDUnit) (rhs: t_PortableSIMDUnit) -> true);
    f_montgomery_multiply_post
    =
    (fun (lhs: t_PortableSIMDUnit) (rhs: t_PortableSIMDUnit) (out: t_PortableSIMDUnit) -> true);
    f_montgomery_multiply
    =
    (fun (lhs: t_PortableSIMDUnit) (rhs: t_PortableSIMDUnit) -> montgomery_multiply lhs rhs);
    f_shift_left_then_reduce_pre = (fun (v_SHIFT_BY: i32) (simd_unit: t_PortableSIMDUnit) -> true);
    f_shift_left_then_reduce_post
    =
    (fun (v_SHIFT_BY: i32) (simd_unit: t_PortableSIMDUnit) (out: t_PortableSIMDUnit) -> true);
    f_shift_left_then_reduce
    =
    (fun (v_SHIFT_BY: i32) (simd_unit: t_PortableSIMDUnit) ->
        shift_left_then_reduce v_SHIFT_BY simd_unit);
    f_power2round_pre = (fun (simd_unit: t_PortableSIMDUnit) -> true);
    f_power2round_post
    =
    (fun (simd_unit: t_PortableSIMDUnit) (out: (t_PortableSIMDUnit & t_PortableSIMDUnit)) -> true);
    f_power2round = (fun (simd_unit: t_PortableSIMDUnit) -> power2round simd_unit);
    f_infinity_norm_exceeds_pre = (fun (simd_unit: t_PortableSIMDUnit) (bound: i32) -> true);
    f_infinity_norm_exceeds_post
    =
    (fun (simd_unit: t_PortableSIMDUnit) (bound: i32) (out: bool) -> true);
    f_infinity_norm_exceeds
    =
    (fun (simd_unit: t_PortableSIMDUnit) (bound: i32) -> infinity_norm_exceeds simd_unit bound);
    f_decompose_pre = (fun (v_GAMMA2: i32) (simd_unit: t_PortableSIMDUnit) -> true);
    f_decompose_post
    =
    (fun
        (v_GAMMA2: i32)
        (simd_unit: t_PortableSIMDUnit)
        (out: (t_PortableSIMDUnit & t_PortableSIMDUnit))
        ->
        true);
    f_decompose
    =
    (fun (v_GAMMA2: i32) (simd_unit: t_PortableSIMDUnit) -> decompose v_GAMMA2 simd_unit);
    f_compute_hint_pre
    =
    (fun (v_GAMMA2: i32) (low: t_PortableSIMDUnit) (high: t_PortableSIMDUnit) -> true);
    f_compute_hint_post
    =
    (fun
        (v_GAMMA2: i32)
        (low: t_PortableSIMDUnit)
        (high: t_PortableSIMDUnit)
        (out: (usize & t_PortableSIMDUnit))
        ->
        true);
    f_compute_hint
    =
    (fun (v_GAMMA2: i32) (low: t_PortableSIMDUnit) (high: t_PortableSIMDUnit) ->
        compute_hint v_GAMMA2 low high);
    f_use_hint_pre
    =
    (fun (v_GAMMA2: i32) (simd_unit: t_PortableSIMDUnit) (hint: t_PortableSIMDUnit) -> true);
    f_use_hint_post
    =
    (fun
        (v_GAMMA2: i32)
        (simd_unit: t_PortableSIMDUnit)
        (hint: t_PortableSIMDUnit)
        (out: t_PortableSIMDUnit)
        ->
        true);
    f_use_hint
    =
    (fun (v_GAMMA2: i32) (simd_unit: t_PortableSIMDUnit) (hint: t_PortableSIMDUnit) ->
        use_hint v_GAMMA2 simd_unit hint);
    f_rejection_sample_less_than_field_modulus_pre
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) -> true);
    f_rejection_sample_less_than_field_modulus_post
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) (out2: (t_Slice i32 & usize)) -> true);
    f_rejection_sample_less_than_field_modulus
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) ->
        let tmp0, out1:(t_Slice i32 & usize) =
          Libcrux_ml_dsa.Simd.Portable.Sample.rejection_sample_less_than_field_modulus randomness
            out
        in
        let out:t_Slice i32 = tmp0 in
        let hax_temp_output:usize = out1 in
        out, hax_temp_output <: (t_Slice i32 & usize));
    f_rejection_sample_less_than_eta_equals_2_pre
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) -> true);
    f_rejection_sample_less_than_eta_equals_2_post
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) (out2: (t_Slice i32 & usize)) -> true);
    f_rejection_sample_less_than_eta_equals_2_
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) ->
        let tmp0, out1:(t_Slice i32 & usize) =
          Libcrux_ml_dsa.Simd.Portable.Sample.rejection_sample_less_than_eta_equals_2_ randomness
            out
        in
        let out:t_Slice i32 = tmp0 in
        let hax_temp_output:usize = out1 in
        out, hax_temp_output <: (t_Slice i32 & usize));
    f_rejection_sample_less_than_eta_equals_4_pre
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) -> true);
    f_rejection_sample_less_than_eta_equals_4_post
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) (out2: (t_Slice i32 & usize)) -> true);
    f_rejection_sample_less_than_eta_equals_4_
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) ->
        let tmp0, out1:(t_Slice i32 & usize) =
          Libcrux_ml_dsa.Simd.Portable.Sample.rejection_sample_less_than_eta_equals_4_ randomness
            out
        in
        let out:t_Slice i32 = tmp0 in
        let hax_temp_output:usize = out1 in
        out, hax_temp_output <: (t_Slice i32 & usize));
    f_gamma1_serialize_pre = (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit) -> true);
    f_gamma1_serialize_post
    =
    (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit) (out: t_Array u8 v_OUTPUT_SIZE) ->
        true);
    f_gamma1_serialize
    =
    (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit) ->
        serialize526929060 v_OUTPUT_SIZE simd_unit);
    f_gamma1_deserialize_pre = (fun (v_GAMMA1_EXPONENT: usize) (serialized: t_Slice u8) -> true);
    f_gamma1_deserialize_post
    =
    (fun (v_GAMMA1_EXPONENT: usize) (serialized: t_Slice u8) (out: t_PortableSIMDUnit) -> true);
    f_gamma1_deserialize
    =
    (fun (v_GAMMA1_EXPONENT: usize) (serialized: t_Slice u8) ->
        deserialize244287932 v_GAMMA1_EXPONENT serialized);
    f_commitment_serialize_pre
    =
    (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit) -> true);
    f_commitment_serialize_post
    =
    (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit) (out: t_Array u8 v_OUTPUT_SIZE) ->
        true);
    f_commitment_serialize
    =
    (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit) ->
        serialize1014427529 v_OUTPUT_SIZE simd_unit);
    f_error_serialize_pre = (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit) -> true);
    f_error_serialize_post
    =
    (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit) (out: t_Array u8 v_OUTPUT_SIZE) ->
        true);
    f_error_serialize
    =
    (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit) ->
        serialize1006998023 v_OUTPUT_SIZE simd_unit);
    f_error_deserialize_pre = (fun (v_ETA: usize) (serialized: t_Slice u8) -> true);
    f_error_deserialize_post
    =
    (fun (v_ETA: usize) (serialized: t_Slice u8) (out: t_PortableSIMDUnit) -> true);
    f_error_deserialize
    =
    (fun (v_ETA: usize) (serialized: t_Slice u8) -> deserialize154437703 v_ETA serialized);
    f_t0_serialize_pre = (fun (simd_unit: t_PortableSIMDUnit) -> true);
    f_t0_serialize_post = (fun (simd_unit: t_PortableSIMDUnit) (out: t_Array u8 (sz 13)) -> true);
    f_t0_serialize = (fun (simd_unit: t_PortableSIMDUnit) -> serialize977980603 simd_unit);
    f_t0_deserialize_pre = (fun (serialized: t_Slice u8) -> true);
    f_t0_deserialize_post = (fun (serialized: t_Slice u8) (out: t_PortableSIMDUnit) -> true);
    f_t0_deserialize = (fun (serialized: t_Slice u8) -> deserialize297775919 serialized);
    f_t1_serialize_pre = (fun (simd_unit: t_PortableSIMDUnit) -> true);
    f_t1_serialize_post = (fun (simd_unit: t_PortableSIMDUnit) (out: t_Array u8 (sz 10)) -> true);
    f_t1_serialize = (fun (simd_unit: t_PortableSIMDUnit) -> serialize300254843 simd_unit);
    f_t1_deserialize_pre = (fun (serialized: t_Slice u8) -> true);
    f_t1_deserialize_post = (fun (serialized: t_Slice u8) (out: t_PortableSIMDUnit) -> true);
    f_t1_deserialize = (fun (serialized: t_Slice u8) -> deserialize960784460 serialized);
    f_ntt_pre = (fun (simd_units: t_Array t_PortableSIMDUnit (sz 32)) -> true);
    f_ntt_post
    =
    (fun
        (simd_units: t_Array t_PortableSIMDUnit (sz 32))
        (out: t_Array t_PortableSIMDUnit (sz 32))
        ->
        true);
    f_ntt = (fun (simd_units: t_Array t_PortableSIMDUnit (sz 32)) -> ntt simd_units);
    f_invert_ntt_at_layer_0_pre
    =
    (fun (simd_unit: t_PortableSIMDUnit) (zeta0: i32) (zeta1: i32) (zeta2: i32) (zeta3: i32) -> true
    );
    f_invert_ntt_at_layer_0_post
    =
    (fun
        (simd_unit: t_PortableSIMDUnit)
        (zeta0: i32)
        (zeta1: i32)
        (zeta2: i32)
        (zeta3: i32)
        (out: t_PortableSIMDUnit)
        ->
        true);
    f_invert_ntt_at_layer_0_
    =
    (fun (simd_unit: t_PortableSIMDUnit) (zeta0: i32) (zeta1: i32) (zeta2: i32) (zeta3: i32) ->
        invert_ntt_at_layer_0_ simd_unit zeta0 zeta1 zeta2 zeta3);
    f_invert_ntt_at_layer_1_pre
    =
    (fun (simd_unit: t_PortableSIMDUnit) (zeta0: i32) (zeta1: i32) -> true);
    f_invert_ntt_at_layer_1_post
    =
    (fun (simd_unit: t_PortableSIMDUnit) (zeta0: i32) (zeta1: i32) (out: t_PortableSIMDUnit) -> true
    );
    f_invert_ntt_at_layer_1_
    =
    (fun (simd_unit: t_PortableSIMDUnit) (zeta0: i32) (zeta1: i32) ->
        invert_ntt_at_layer_1_ simd_unit zeta0 zeta1);
    f_invert_ntt_at_layer_2_pre = (fun (simd_unit: t_PortableSIMDUnit) (zeta: i32) -> true);
    f_invert_ntt_at_layer_2_post
    =
    (fun (simd_unit: t_PortableSIMDUnit) (zeta: i32) (out: t_PortableSIMDUnit) -> true);
    f_invert_ntt_at_layer_2_
    =
    fun (simd_unit: t_PortableSIMDUnit) (zeta: i32) -> invert_ntt_at_layer_2_ simd_unit zeta
  }

and ntt_at_layer_3_plus (v_LAYER zeta_i: usize) (re: t_Array t_PortableSIMDUnit (sz 32))
    : (usize & t_Array t_PortableSIMDUnit (sz 32)) =
  let step:usize = sz 1 <<! v_LAYER in
  let (re, zeta_i), hax_temp_output:((t_Array t_PortableSIMDUnit (sz 32) & usize) & Prims.unit) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (sz 128 >>! v_LAYER <: usize)
      (fun temp_0_ temp_1_ ->
          let re, zeta_i:(t_Array t_PortableSIMDUnit (sz 32) & usize) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (re, zeta_i <: (t_Array t_PortableSIMDUnit (sz 32) & usize))
      (fun temp_0_ round ->
          let re, zeta_i:(t_Array t_PortableSIMDUnit (sz 32) & usize) = temp_0_ in
          let round:usize = round in
          let zeta_i:usize = zeta_i +! sz 1 in
          let offset:usize =
            ((round *! step <: usize) *! sz 2 <: usize) /!
            Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT
          in
          let step_by:usize = step /! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT in
          let re:t_Array t_PortableSIMDUnit (sz 32) =
            Rust_primitives.Hax.Folds.fold_range offset
              (offset +! step_by <: usize)
              (fun re temp_1_ ->
                  let re:t_Array t_PortableSIMDUnit (sz 32) = re in
                  let _:usize = temp_1_ in
                  true)
              re
              (fun re j ->
                  let re:t_Array t_PortableSIMDUnit (sz 32) = re in
                  let j:usize = j in
                  let t:t_PortableSIMDUnit =
                    Libcrux_ml_dsa.Simd.Traits.montgomery_multiply_by_fer #t_PortableSIMDUnit
                      (re.[ j +! step_by <: usize ] <: t_PortableSIMDUnit)
                      (Libcrux_ml_dsa.Simd.Traits.v_ZETAS_TIMES_MONTGOMERY_R.[ zeta_i ] <: i32)
                  in
                  let re:t_Array t_PortableSIMDUnit (sz 32) =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                      (j +! step_by <: usize)
                      (subtract (re.[ j ] <: t_PortableSIMDUnit) t <: t_PortableSIMDUnit)
                  in
                  let re:t_Array t_PortableSIMDUnit (sz 32) =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                      j
                      (add (re.[ j ] <: t_PortableSIMDUnit) t <: t_PortableSIMDUnit)
                  in
                  re)
          in
          re, zeta_i <: (t_Array t_PortableSIMDUnit (sz 32) & usize))
  in
  zeta_i, re <: (usize & t_Array t_PortableSIMDUnit (sz 32))
