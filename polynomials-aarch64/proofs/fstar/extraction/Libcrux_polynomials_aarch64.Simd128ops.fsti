module Libcrux_polynomials_aarch64.Simd128ops
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_BARRETT_MULTIPLIER: i16 = 20159s

val mask_n_least_significant_bits (coefficient_bits: i16)
    : Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

val barrett_reduce_int16x8_t (v: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val compress_int32x4_t (v_COEFFICIENT_BITS: i32) (v: Core.Core_arch.Arm_shared.Neon.t_uint32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint32x4_t Prims.l_True (fun _ -> Prims.l_True)

val decompress_uint32x4_t (v_COEFFICIENT_BITS: i32) (v: Core.Core_arch.Arm_shared.Neon.t_uint32x4_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_uint32x4_t Prims.l_True (fun _ -> Prims.l_True)

val montgomery_reduce_int16x8_t (low high: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply_by_constant_int16x8_t
      (v: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
      (c: i16)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply_int16x8_t (v c: Core.Core_arch.Arm_shared.Neon.t_int16x8_t)
    : Prims.Pure Core.Core_arch.Arm_shared.Neon.t_int16x8_t Prims.l_True (fun _ -> Prims.l_True)

type t_SIMD128Vector = {
  f_low:Core.Core_arch.Arm_shared.Neon.t_int16x8_t;
  f_high:Core.Core_arch.Arm_shared.Neon.t_int16x8_t
}

val v_ZERO: Prims.unit -> Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val add (lhs rhs: t_SIMD128Vector) : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val barrett_reduce (v: t_SIMD128Vector)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val bitwise_and_with_constant (v: t_SIMD128Vector) (c: i16)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val compress (v_COEFFICIENT_BITS: i32) (v: t_SIMD128Vector)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val compress_1_ (v: t_SIMD128Vector)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val cond_subtract_3329_ (v: t_SIMD128Vector)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val decompress (v_COEFFICIENT_BITS: i32) (v: t_SIMD128Vector)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val deserialize_1_ (a: t_Slice u8) : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val deserialize_10_ (v: t_Slice u8)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val deserialize_11_ (v: t_Slice u8)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val deserialize_12_ (v: t_Slice u8)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val deserialize_4_ (v: t_Slice u8) : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val deserialize_5_ (v: t_Slice u8) : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val from_i16_array (array: t_Array i16 (sz 16))
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val inv_ntt_layer_1_step (v: t_SIMD128Vector) (zeta1 zeta2 zeta3 zeta4: i16)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val inv_ntt_layer_2_step (v: t_SIMD128Vector) (zeta1 zeta2: i16)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val inv_ntt_layer_3_step (v: t_SIMD128Vector) (zeta: i16)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply_by_constant (v: t_SIMD128Vector) (c: i16)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val multiply_by_constant (v: t_SIMD128Vector) (c: i16)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val ntt_layer_1_step (v: t_SIMD128Vector) (zeta1 zeta2 zeta3 zeta4: i16)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val ntt_layer_2_step (v: t_SIMD128Vector) (zeta1 zeta2: i16)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val ntt_layer_3_step (v: t_SIMD128Vector) (zeta: i16)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val ntt_multiply (lhs rhs: t_SIMD128Vector) (zeta1 zeta2 zeta3 zeta4: i16)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val serialize_1_ (v: t_SIMD128Vector)
    : Prims.Pure (t_Array u8 (sz 2)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_10_ (v: t_SIMD128Vector)
    : Prims.Pure (t_Array u8 (sz 20)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_12_ (v: t_SIMD128Vector)
    : Prims.Pure (t_Array u8 (sz 24)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_4_ (v: t_SIMD128Vector)
    : Prims.Pure (t_Array u8 (sz 8)) Prims.l_True (fun _ -> Prims.l_True)

val shift_left (v_SHIFT_BY: i32) (lhs: t_SIMD128Vector)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val shift_right (v_SHIFT_BY: i32) (v: t_SIMD128Vector)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val sub (lhs rhs: t_SIMD128Vector) : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val to_i16_array (v: t_SIMD128Vector)
    : Prims.Pure (t_Array i16 (sz 16)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_11_ (v: t_SIMD128Vector)
    : Prims.Pure (t_Array u8 (sz 22)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_5_ (v: t_SIMD128Vector)
    : Prims.Pure (t_Array u8 (sz 10)) Prims.l_True (fun _ -> Prims.l_True)
