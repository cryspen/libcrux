module Libcrux_platform.Macos_arm
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

assume
val cstr': src: t_Slice i8 -> Prims.Pure string Prims.l_True (fun _ -> Prims.l_True)

let cstr = cstr'

assume
val actually_arm': Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let actually_arm = actually_arm'

assume
val check': feature: t_Slice i8 -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let check = check'

assume
val sysctl': Prims.unit -> Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

let sysctl = sysctl'

assume
val aes': Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let aes = aes'

assume
val adv_simd': Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let adv_simd = adv_simd'

assume
val pmull': Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let pmull = pmull'

assume
val sha256': Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let sha256 = sha256'

assume
val init': Prims.unit -> Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

let init = init'
