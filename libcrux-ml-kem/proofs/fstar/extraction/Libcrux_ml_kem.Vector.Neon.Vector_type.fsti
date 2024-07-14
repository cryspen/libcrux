module Libcrux_ml_kem.Vector.Neon.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_SIMD128Vector = {
  f_low:u8;
  f_high:u8
}

val v_ZERO: Prims.unit -> Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val from_i16_array (array: t_Slice i16)
    : Prims.Pure t_SIMD128Vector Prims.l_True (fun _ -> Prims.l_True)

val to_i16_array (v: t_SIMD128Vector)
    : Prims.Pure (t_Array i16 (sz 16)) Prims.l_True (fun _ -> Prims.l_True)
