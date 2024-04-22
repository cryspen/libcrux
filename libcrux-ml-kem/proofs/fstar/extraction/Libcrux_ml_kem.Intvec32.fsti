module Libcrux_ml_kem.Intvec32
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_SIZE_VEC: usize = sz 8

type t_IntVec = { f_elements:t_Array i32 (sz 8) }

let v_ZERO_VEC: t_IntVec = { f_elements = Rust_primitives.Hax.repeat 0l (sz 8) } <: t_IntVec

val add_int_vec (lhs rhs: t_IntVec) : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val add_int_vec_constant (lhs: t_IntVec) (rhs: i32)
    : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val barrett_reduce_int_vec (a: t_IntVec) : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val bit_and_int_vec_constant (lhs: t_IntVec) (rhs: i32)
    : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val compress_1_int_vec (a: t_IntVec) : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val compress_int_vec (coefficient_bits: u8) (a: t_IntVec)
    : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val deserialize_10_int_vec (bytes: t_Slice u8)
    : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val deserialize_11_int_vec (bytes: t_Slice u8)
    : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val deserialize_12_int_vec (bytes: t_Slice u8)
    : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val deserialize_1_int_vec (a: u8) : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val deserialize_4_int_vec (bytes: t_Slice u8)
    : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val deserialize_5_int_vec (bytes: t_Slice u8)
    : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val int_vec_from_i32_array (a: t_Array i32 (sz 8))
    : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val int_vec_to_i32_array (a: t_IntVec)
    : Prims.Pure (t_Array i32 (sz 8)) Prims.l_True (fun _ -> Prims.l_True)

val inv_ntt_layer_1_int_vec_step (a: t_IntVec) (zeta1 zeta2: i32)
    : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val inv_ntt_layer_2_int_vec_step (a: t_IntVec) (zeta: i32)
    : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val left_shift_int_vec (lhs: t_IntVec) (rhs: u8)
    : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val modulus_int_vec_constant_var_time (lhs: t_IntVec) (rhs: i32)
    : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val montgomery_reduce_int_vec (a: t_IntVec)
    : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val mul_int_vec_constant (lhs: t_IntVec) (rhs: i32)
    : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val ntt_layer_1_int_vec_step (a: t_IntVec) (zeta1 zeta2: i32)
    : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val ntt_layer_2_int_vec_step (a: t_IntVec) (zeta: i32)
    : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val ntt_multiply_int_vec (lhs rhs: t_IntVec) (zeta0 zeta1: i32)
    : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val right_shift_int_vec (lhs: t_IntVec) (rhs: u8)
    : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)

val serialize_10_int_vec (a: t_IntVec)
    : Prims.Pure (t_Array u8 (sz 10)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_11_int_vec (a: t_IntVec)
    : Prims.Pure (t_Array u8 (sz 11)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_12_int_vec (a: t_IntVec)
    : Prims.Pure (t_Array u8 (sz 12)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_1_int_vec (a: t_IntVec) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val serialize_4_int_vec (a: t_IntVec)
    : Prims.Pure (t_Array u8 (sz 4)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_5_int_vec (a: t_IntVec)
    : Prims.Pure (t_Array u8 (sz 5)) Prims.l_True (fun _ -> Prims.l_True)

val sub_int_vec (lhs rhs: t_IntVec) : Prims.Pure t_IntVec Prims.l_True (fun _ -> Prims.l_True)
