module Libcrux_ml_kem.Intvec
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let add_int_vec (lhs rhs: Libcrux_ml_kem.Intvec32.t_IntVec) =
  Libcrux_ml_kem.Intvec32.add_int_vec lhs rhs

let add_int_vec_constant (lhs: Libcrux_ml_kem.Intvec32.t_IntVec) (rhs: i32) =
  Libcrux_ml_kem.Intvec32.add_int_vec_constant lhs rhs

let barrett_reduce_int_vec (a: Libcrux_ml_kem.Intvec32.t_IntVec) =
  Libcrux_ml_kem.Intvec32.barrett_reduce_int_vec a

let bit_and_int_vec_constant (lhs: Libcrux_ml_kem.Intvec32.t_IntVec) (rhs: i32) =
  Libcrux_ml_kem.Intvec32.bit_and_int_vec_constant lhs rhs

let compress_1_int_vec (a: Libcrux_ml_kem.Intvec32.t_IntVec) =
  Libcrux_ml_kem.Intvec32.compress_1_int_vec a

let compress_int_vec (coefficient_bits: u8) (a: Libcrux_ml_kem.Intvec32.t_IntVec) =
  Libcrux_ml_kem.Intvec32.compress_int_vec coefficient_bits a

let deserialize_10_int_vec (bytes: t_Slice u8) =
  Libcrux_ml_kem.Intvec32.deserialize_10_int_vec bytes

let deserialize_11_int_vec (bytes: t_Slice u8) =
  Libcrux_ml_kem.Intvec32.deserialize_11_int_vec bytes

let deserialize_12_int_vec (bytes: t_Slice u8) =
  Libcrux_ml_kem.Intvec32.deserialize_12_int_vec bytes

let deserialize_1_int_vec (a: u8) = Libcrux_ml_kem.Intvec32.deserialize_1_int_vec a

let deserialize_4_int_vec (bytes: t_Slice u8) = Libcrux_ml_kem.Intvec32.deserialize_4_int_vec bytes

let deserialize_5_int_vec (bytes: t_Slice u8) = Libcrux_ml_kem.Intvec32.deserialize_5_int_vec bytes

let int_vec_from_i32_array (a: t_Array i32 (sz 8)) =
  Libcrux_ml_kem.Intvec32.int_vec_from_i32_array a

let int_vec_to_i32_array (a: Libcrux_ml_kem.Intvec32.t_IntVec) =
  Libcrux_ml_kem.Intvec32.int_vec_to_i32_array a

let inv_ntt_layer_1_int_vec_step (a: Libcrux_ml_kem.Intvec32.t_IntVec) (zeta1 zeta2: i32) =
  Libcrux_ml_kem.Intvec32.inv_ntt_layer_1_int_vec_step a zeta1 zeta2

let inv_ntt_layer_2_int_vec_step (a: Libcrux_ml_kem.Intvec32.t_IntVec) (zeta: i32) =
  Libcrux_ml_kem.Intvec32.inv_ntt_layer_2_int_vec_step a zeta

let left_shift_int_vec (lhs: Libcrux_ml_kem.Intvec32.t_IntVec) (rhs: u8) =
  Libcrux_ml_kem.Intvec32.left_shift_int_vec lhs rhs

let modulus_int_vec_constant_var_time (lhs: Libcrux_ml_kem.Intvec32.t_IntVec) (rhs: i32) =
  Libcrux_ml_kem.Intvec32.modulus_int_vec_constant_var_time lhs rhs

let montgomery_reduce_int_vec (a: Libcrux_ml_kem.Intvec32.t_IntVec) =
  Libcrux_ml_kem.Intvec32.montgomery_reduce_int_vec a

let mul_int_vec_constant (lhs: Libcrux_ml_kem.Intvec32.t_IntVec) (rhs: i32) =
  Libcrux_ml_kem.Intvec32.mul_int_vec_constant lhs rhs

let montgomery_multiply_fe_by_fer_int_vec (a: Libcrux_ml_kem.Intvec32.t_IntVec) (b: i32) =
  let t:Libcrux_ml_kem.Intvec32.t_IntVec = mul_int_vec_constant a b in
  montgomery_reduce_int_vec t

let to_standard_domain_int_vec (a: Libcrux_ml_kem.Intvec32.t_IntVec) =
  let t:Libcrux_ml_kem.Intvec32.t_IntVec =
    mul_int_vec_constant a Libcrux_ml_kem.Arithmetic.v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS
  in
  montgomery_reduce_int_vec t

let ntt_layer_1_int_vec_step (a: Libcrux_ml_kem.Intvec32.t_IntVec) (zeta1 zeta2: i32) =
  Libcrux_ml_kem.Intvec32.ntt_layer_1_int_vec_step a zeta1 zeta2

let ntt_layer_2_int_vec_step (a: Libcrux_ml_kem.Intvec32.t_IntVec) (zeta: i32) =
  Libcrux_ml_kem.Intvec32.ntt_layer_2_int_vec_step a zeta

let ntt_multiply_int_vec (lhs rhs: Libcrux_ml_kem.Intvec32.t_IntVec) (zeta0 zeta1: i32) =
  Libcrux_ml_kem.Intvec32.ntt_multiply_int_vec lhs rhs zeta0 zeta1

let right_shift_int_vec (lhs: Libcrux_ml_kem.Intvec32.t_IntVec) (rhs: u8) =
  Libcrux_ml_kem.Intvec32.right_shift_int_vec lhs rhs

let decompress_int_vec (coefficient_bits: u8) (a: Libcrux_ml_kem.Intvec32.t_IntVec) =
  let decompressed:Libcrux_ml_kem.Intvec32.t_IntVec =
    mul_int_vec_constant a Libcrux_ml_kem.Constants.v_FIELD_MODULUS
  in
  let decompressed:Libcrux_ml_kem.Intvec32.t_IntVec =
    add_int_vec_constant (left_shift_int_vec decompressed 1uy <: Libcrux_ml_kem.Intvec32.t_IntVec)
      (1l <<! coefficient_bits <: i32)
  in
  let decompressed:Libcrux_ml_kem.Intvec32.t_IntVec =
    right_shift_int_vec decompressed (coefficient_bits +! 1uy <: u8)
  in
  decompressed

let to_unsigned_representative_int_vec (a: Libcrux_ml_kem.Intvec32.t_IntVec) =
  let t:Libcrux_ml_kem.Intvec32.t_IntVec = right_shift_int_vec a 31uy in
  let fm:Libcrux_ml_kem.Intvec32.t_IntVec =
    bit_and_int_vec_constant t Libcrux_ml_kem.Constants.v_FIELD_MODULUS
  in
  add_int_vec a fm

let serialize_10_int_vec (a: Libcrux_ml_kem.Intvec32.t_IntVec) =
  Libcrux_ml_kem.Intvec32.serialize_10_int_vec a

let serialize_11_int_vec (a: Libcrux_ml_kem.Intvec32.t_IntVec) =
  Libcrux_ml_kem.Intvec32.serialize_11_int_vec a

let serialize_12_int_vec (a: Libcrux_ml_kem.Intvec32.t_IntVec) =
  Libcrux_ml_kem.Intvec32.serialize_12_int_vec a

let serialize_1_int_vec (a: Libcrux_ml_kem.Intvec32.t_IntVec) =
  Libcrux_ml_kem.Intvec32.serialize_1_int_vec a

let serialize_4_int_vec (a: Libcrux_ml_kem.Intvec32.t_IntVec) =
  Libcrux_ml_kem.Intvec32.serialize_4_int_vec a

let serialize_5_int_vec (a: Libcrux_ml_kem.Intvec32.t_IntVec) =
  Libcrux_ml_kem.Intvec32.serialize_5_int_vec a

let sub_int_vec (lhs rhs: Libcrux_ml_kem.Intvec32.t_IntVec) =
  Libcrux_ml_kem.Intvec32.sub_int_vec lhs rhs

let decompress_1_int_vec (a: Libcrux_ml_kem.Intvec32.t_IntVec) =
  bit_and_int_vec_constant (sub_int_vec v_ZERO_VEC a <: Libcrux_ml_kem.Intvec32.t_IntVec) 1665l
