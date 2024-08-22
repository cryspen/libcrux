module Libcrux_ml_kem.Vector.Avx2.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let ntt_multiply__PERMUTE_WITH: i32 = 216l

val inv_ntt_layer_1_step (vector: u8) (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val inv_ntt_layer_2_step (vector: u8) (zeta0 zeta1: i16)
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val inv_ntt_layer_3_step (vector: u8) (zeta: i16)
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val ntt_layer_1_step (vector: u8) (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val ntt_layer_2_step (vector: u8) (zeta0 zeta1: i16)
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val ntt_layer_3_step (vector: u8) (zeta: i16) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val ntt_multiply (lhs rhs: u8) (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
