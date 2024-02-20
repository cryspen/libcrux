module Libcrux_platform.Platform
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val bmi2_adx_support: Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val simd256_support: Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val x25519_support: Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val adv_simd_support: Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val aes_ni_support: Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val pmull_support: Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val sha256_support: Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val simd128_support: Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)
