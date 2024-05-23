module Libcrux_platform.Macos_arm
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Check that we're actually on an ARM mac.
/// When this returns false, no other function in here must be called.
val actually_arm: Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val adv_simd: Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val aes: Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val check (feature: t_Slice i8) : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val cstr (src: t_Slice i8) : Prims.Pure string Prims.l_True (fun _ -> Prims.l_True)

/// Initialize CPU detection.
val init: Prims.unit -> Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

val pmull: Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val sha256: Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val sysctl: Prims.unit -> Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

let sysctl__ADV_SIMD_STR: t_Array i8 (sz 20) = Rust_primitives.Hax.dropped_body

let sysctl__FEAT_AES_STR: t_Array i8 (sz 25) = Rust_primitives.Hax.dropped_body

let sysctl__FEAT_PMULL_STR: t_Array i8 (sz 27) = Rust_primitives.Hax.dropped_body

let sysctl__FEAT_SHA256_STR: t_Array i8 (sz 28) = Rust_primitives.Hax.dropped_body
