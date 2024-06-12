module Libcrux_ml_kem.Vector.Avx2.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_BARRETT_MULTIPLIER: i16 = Rust_primitives.Hax.dropped_body

val add (lhs rhs: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

/// See Section 3.2 of the implementation notes document for an explanation
/// of this code.
val barrett_reduce (vector: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val bitwise_and_with_constant (vector: Core.Core_arch.X86.t____m256i) (constant: i16)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val cond_subtract_3329_ (vector: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply_by_constant (vector: Core.Core_arch.X86.t____m256i) (constant: i16)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply_by_constants (v c: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply_m128i_by_constants (v c: Core.Core_arch.X86.t____m128i)
    : Prims.Pure Core.Core_arch.X86.t____m128i Prims.l_True (fun _ -> Prims.l_True)

val montgomery_reduce_i32s (v: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val multiply_by_constant (vector: Core.Core_arch.X86.t____m256i) (constant: i16)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val shift_right (v_SHIFT_BY: i32) (vector: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)

val sub (lhs rhs: Core.Core_arch.X86.t____m256i)
    : Prims.Pure Core.Core_arch.X86.t____m256i Prims.l_True (fun _ -> Prims.l_True)
