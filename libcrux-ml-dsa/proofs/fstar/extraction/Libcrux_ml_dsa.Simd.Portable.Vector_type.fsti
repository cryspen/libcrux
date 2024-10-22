module Libcrux_ml_dsa.Simd.Portable.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

type t_PortableSIMDUnit = { f_coefficients:t_Array i32 (sz 8) }

val from_coefficient_array (array: t_Slice i32)
    : Prims.Pure t_PortableSIMDUnit Prims.l_True (fun _ -> Prims.l_True)

val to_coefficient_array (x: t_PortableSIMDUnit)
    : Prims.Pure (t_Array i32 (sz 8)) Prims.l_True (fun _ -> Prims.l_True)

val v_ZERO: Prims.unit -> Prims.Pure t_PortableSIMDUnit Prims.l_True (fun _ -> Prims.l_True)
