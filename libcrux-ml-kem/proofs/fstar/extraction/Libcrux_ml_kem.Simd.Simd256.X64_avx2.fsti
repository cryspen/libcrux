module Libcrux_ml_kem.Simd.Simd256.X64_avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_Vec = Core.Core_arch.X86.t____m256i

val add (a b: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val v_and (a b: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val load (v: i32) : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val load_i32s (e0 e1 e2 e3 e4 e5 e6 e7: i32)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val load_i8s
      (e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31:
          i8)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val load_vec (array: t_Array i32 (sz 8))
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val mul (a b: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

/// Shifting in 0
val shlli (v_SHIFT_BY: i32) (a: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

/// Shifting in 0
val shllv (a count: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

/// Signed shift
val shr (v_SHIFT_BY: i32) (a: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

/// Shifting in 0
val shrli (v_SHIFT_BY: i32) (a: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

/// Shifting in 0
val shrli16 (v_SHIFT_BY: i32) (a: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

/// Shifting in 0
val shrllv (a count: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val shuffle (a b: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val store (v: Core.Core_arch.X86.t____m256i)
    : Prims.Pure (t_Array i32 (sz 8)) Prims.l_True (fun _ -> Prims.l_True)

val storei16 (v_INDEX: i32) (v: Core.Core_arch.X86.t____m256i)
    : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val sub (a b: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val xor (a b: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val zero: Prims.unit
  -> Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)
