module Libcrux_platform.Platform
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

assume
val adv_simd_support': Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let adv_simd_support = adv_simd_support'

assume
val aes_ni_support': Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let aes_ni_support = aes_ni_support'

assume
val bmi2_adx_support': Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let bmi2_adx_support = bmi2_adx_support'

assume
val pmull_support': Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let pmull_support = pmull_support'

assume
val sha256_support': Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let sha256_support = sha256_support'

assume
val simd128_support': Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let simd128_support = simd128_support'

assume
val simd256_support': Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let simd256_support = simd256_support'

assume
val x25519_support': Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let x25519_support = x25519_support'
