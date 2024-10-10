module Libcrux_ml_kem.Vector.Portable.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

/// This is calculated as ⌊(BARRETT_R / FIELD_MODULUS) + 1/2⌋
let v_BARRETT_MULTIPLIER: i32 = Rust_primitives.mk_i32 20159

let v_MONTGOMERY_SHIFT: u8 = Rust_primitives.mk_u8 16

let v_MONTGOMERY_R: i32 = Rust_primitives.mk_i32 1 <<! v_MONTGOMERY_SHIFT

val get_n_least_significant_bits (n: u8) (value: u32)
    : Prims.Pure u32
      (requires n <=. Rust_primitives.mk_u8 16)
      (ensures
        fun result ->
          let result:u32 = result in
          v result == v value % pow2 (v n))

/// Signed Barrett Reduction
/// Given an input `value`, `barrett_reduce` outputs a representative `result`
/// such that:
/// - result ≡ value (mod FIELD_MODULUS)
/// - the absolute value of `result` is bound as follows:
/// `|result| ≤ FIELD_MODULUS / 2 · (|value|/BARRETT_R + 1)
///
/// Note: The input bound is 28296 to prevent overflow in the multiplication of quotient by FIELD_MODULUS
///
val barrett_reduce_element (value: i16)
    : Prims.Pure i16
      (requires Spec.Utils.is_i16b 28296 value)
      (ensures
        fun result ->
          let result:i16 = result in
          Spec.Utils.is_i16b 3328 result /\ v result % 3329 == v value % 3329)

/// Signed Montgomery Reduction
/// Given an input `value`, `montgomery_reduce` outputs a representative `o`
/// such that:
/// - o ≡ value · MONTGOMERY_R^(-1) (mod FIELD_MODULUS)
/// - the absolute value of `o` is bound as follows:
/// `|result| ≤ ceil(|value| / MONTGOMERY_R) + 1665
/// In particular, if `|value| ≤ FIELD_MODULUS-1 * FIELD_MODULUS-1`, then `|o| <= FIELD_MODULUS-1`.
/// And, if `|value| ≤ pow2 16 * FIELD_MODULUS-1`, then `|o| <= FIELD_MODULUS + 1664
///
val montgomery_reduce_element (value: i32)
    : Prims.Pure i16
      (requires Spec.Utils.is_i32b (3328 * pow2 16) value)
      (ensures
        fun result ->
          let result:i16 = result in
          Spec.Utils.is_i16b (3328 + 1665) result /\
          (Spec.Utils.is_i32b (3328 * pow2 15) value ==> Spec.Utils.is_i16b 3328 result) /\
          v result % 3329 == (v value * 169) % 3329)

/// If `fe` is some field element \'x\' of the Kyber field and `fer` is congruent to
/// `y · MONTGOMERY_R`, this procedure outputs a value that is congruent to
/// `x · y`, as follows:
///    `fe · fer ≡ x · y · MONTGOMERY_R (mod FIELD_MODULUS)`
/// `montgomery_reduce` takes the value `x · y · MONTGOMERY_R` and outputs a representative
/// `x · y · MONTGOMERY_R * MONTGOMERY_R^{-1} ≡ x · y (mod FIELD_MODULUS)`.
val montgomery_multiply_fe_by_fer (fe fer: i16)
    : Prims.Pure i16
      (requires Spec.Utils.is_i16b 1664 fer)
      (ensures
        fun result ->
          let result:i16 = result in
          Spec.Utils.is_i16b 3328 result /\ v result % 3329 == (v fe * v fer * 169) % 3329)

val add (lhs rhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires
        forall i.
          i < 16 ==>
          Spec.Utils.is_intb (pow2 15 - 1)
            (v (Seq.index lhs.f_elements i) + v (Seq.index rhs.f_elements i)))
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          forall i.
            i < 16 ==>
            (v (Seq.index result.f_elements i) ==
              v (Seq.index lhs.f_elements i) + v (Seq.index rhs.f_elements i)))

val barrett_reduce (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires Spec.Utils.is_i16b_array 28296 vec.f_elements)
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          Spec.Utils.is_i16b_array 3328 result.f_elements /\
          (forall i.
              (v (Seq.index result.f_elements i) % 3329) == (v (Seq.index vec.f_elements i) % 3329))
      )

val bitwise_and_with_constant
      (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (c: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          result.f_elements == Spec.Utils.map_array (fun x -> x &. c) (vec.f_elements))

/// Note: This function is not secret independent
/// Only use with public values.
val cond_subtract_3329_ (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires Spec.Utils.is_i16b_array (pow2 12 - 1) vec.f_elements)
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          result.f_elements ==
          Spec.Utils.map_array (fun x -> if x >=. mk_i16 3329 then x -! (mk_i16 3329) else x)
            (vec.f_elements))

val montgomery_multiply_by_constant
      (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (c: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires Spec.Utils.is_i16b 1664 c)
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          Spec.Utils.is_i16b_array 3328 result.f_elements /\
          (forall i.
              i < 16 ==>
              (v (Seq.index result.f_elements i) % 3329 ==
                (v (Seq.index vec.f_elements i) * v c * 169) % 3329)))

val multiply_by_constant (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (c: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires
        forall i. i < 16 ==> Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index vec.f_elements i) * v c)
      )
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          forall i.
            i < 16 ==> (v (Seq.index result.f_elements i) == v (Seq.index vec.f_elements i) * v c))

val shift_right (v_SHIFT_BY: i32) (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires v_SHIFT_BY >=. Rust_primitives.mk_i32 0 && v_SHIFT_BY <. Rust_primitives.mk_i32 16)
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          (v_SHIFT_BY >=. (mk_i32 0) /\ v_SHIFT_BY <. (mk_i32 16)) ==>
          result.f_elements == Spec.Utils.map_array (fun x -> x >>! v_SHIFT_BY) (vec.f_elements))

val sub (lhs rhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires
        forall i.
          i < 16 ==>
          Spec.Utils.is_intb (pow2 15 - 1)
            (v (Seq.index lhs.f_elements i) - v (Seq.index rhs.f_elements i)))
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          forall i.
            i < 16 ==>
            (v (Seq.index result.f_elements i) ==
              v (Seq.index lhs.f_elements i) - v (Seq.index rhs.f_elements i)))
