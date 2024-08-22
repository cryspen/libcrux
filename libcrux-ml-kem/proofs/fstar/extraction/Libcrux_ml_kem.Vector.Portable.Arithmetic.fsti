module Libcrux_ml_kem.Vector.Portable.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// This is calculated as ⌊(BARRETT_R / FIELD_MODULUS) + 1/2⌋
let v_BARRETT_MULTIPLIER: i32 = 20159l

let v_BARRETT_SHIFT: i32 = 26l

let v_BARRETT_R: i32 = 1l <<! v_BARRETT_SHIFT

let v_MONTGOMERY_SHIFT: u8 = 16uy

let v_MONTGOMERY_R: i32 = 1l <<! v_MONTGOMERY_SHIFT

val get_n_least_significant_bits (n: u8) (value: u32)
    : Prims.Pure u32
      (requires n =. 4uy || n =. 5uy || n =. 10uy || n =. 11uy || n =. v_MONTGOMERY_SHIFT)
      (ensures
        fun result ->
          let result:u32 = result in
          result <.
          (Core.Num.impl__u32__pow 2ul
              (Core.Convert.f_into #u8 #u32 #FStar.Tactics.Typeclasses.solve n <: u32)
            <:
            u32))

/// Signed Barrett Reduction
/// Given an input `value`, `barrett_reduce` outputs a representative `result`
/// such that:
/// - result ≡ value (mod FIELD_MODULUS)
/// - the absolute value of `result` is bound as follows:
/// `|result| ≤ FIELD_MODULUS / 2 · (|value|/BARRETT_R + 1)
/// In particular, if `|value| < BARRETT_R`, then `|result| < FIELD_MODULUS`.
val barrett_reduce_element (value: i16)
    : Prims.Pure i16
      (requires
        (Core.Convert.f_from #i32 #i16 #FStar.Tactics.Typeclasses.solve value <: i32) >.
        (Core.Ops.Arith.Neg.neg v_BARRETT_R <: i32) &&
        (Core.Convert.f_from #i32 #i16 #FStar.Tactics.Typeclasses.solve value <: i32) <. v_BARRETT_R
      )
      (ensures
        fun result ->
          let result:i16 = result in
          result >. (Core.Ops.Arith.Neg.neg Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) &&
          result <. Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS)

/// Signed Montgomery Reduction
/// Given an input `value`, `montgomery_reduce` outputs a representative `o`
/// such that:
/// - o ≡ value · MONTGOMERY_R^(-1) (mod FIELD_MODULUS)
/// - the absolute value of `o` is bound as follows:
/// `|result| ≤ (|value| / MONTGOMERY_R) + (FIELD_MODULUS / 2)
/// In particular, if `|value| ≤ FIELD_MODULUS * MONTGOMERY_R`, then `|o| < (3 · FIELD_MODULUS) / 2`.
val montgomery_reduce_element (value: i32)
    : Prims.Pure i16
      (requires
        value >=.
        ((Core.Ops.Arith.Neg.neg (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) <: i32)
            <:
            i32) *!
          v_MONTGOMERY_R
          <:
          i32) &&
        value <=.
        ((cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) <: i32) *! v_MONTGOMERY_R
          <:
          i32))
      (ensures
        fun result ->
          let result:i16 = result in
          result >=.
          ((Core.Ops.Arith.Neg.neg (3s *! Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16)
              <:
              i16) /!
            2s
            <:
            i16) &&
          result <=. ((3s *! Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) /! 2s <: i16))

/// If `fe` is some field element 'x' of the Kyber field and `fer` is congruent to
/// `y · MONTGOMERY_R`, this procedure outputs a value that is congruent to
/// `x · y`, as follows:
///    `fe · fer ≡ x · y · MONTGOMERY_R (mod FIELD_MODULUS)`
/// `montgomery_reduce` takes the value `x · y · MONTGOMERY_R` and outputs a representative
/// `x · y · MONTGOMERY_R * MONTGOMERY_R^{-1} ≡ x · y (mod FIELD_MODULUS)`.
val montgomery_multiply_fe_by_fer (fe fer: i16)
    : Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

val add (lhs rhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val barrett_reduce (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val bitwise_and_with_constant
      (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (c: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val cond_subtract_3329_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val montgomery_multiply_by_constant
      (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (c: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val multiply_by_constant (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (c: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val shift_right (v_SHIFT_BY: i32) (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val sub (lhs rhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)
