module Libcrux_ml_dsa.Simd.Portable.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Portable.Vector_type in
  ()

let v_MONTGOMERY_SHIFT: u8 = mk_u8 32

val add (lhs rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      (requires
        Libcrux_ml_dsa.Simd.Traits.Specs.add_pre lhs
            .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
          rhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values)
      (ensures
        fun lhs_future ->
          let lhs_future:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = lhs_future in
          Libcrux_ml_dsa.Simd.Traits.Specs.add_post lhs
              .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
            rhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
            lhs_future.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values)

val subtract (lhs rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      (requires
        Libcrux_ml_dsa.Simd.Traits.Specs.sub_pre lhs
            .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
          rhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values)
      (ensures
        fun lhs_future ->
          let lhs_future:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = lhs_future in
          Libcrux_ml_dsa.Simd.Traits.Specs.sub_post lhs
              .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
            rhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
            lhs_future.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values)

val get_n_least_significant_bits (n: u8) (value: u64)
    : Prims.Pure u64
      (requires n <=. mk_u8 32)
      (ensures
        fun result ->
          let result:u64 = result in
          v result == v value % pow2 (v n))

val montgomery_reduce_element (value: i64)
    : Prims.Pure i32
      (requires Spec.Utils.is_i64b (8380416 * pow2 32) value)
      (ensures
        fun result ->
          let result:i32 = result in
          Spec.Utils.is_i32b (8380416 + 4190209) result /\
          (Spec.Utils.is_i64b (8380416 * pow2 31) value ==> Spec.Utils.is_i32b 8380416 result) /\
          v result % 8380417 == (v value * 8265825) % 8380417)

val montgomery_multiply_fe_by_fer (fe fer: i32)
    : Prims.Pure i32
      (requires Spec.Utils.is_i32b 4190208 fer)
      (ensures
        fun result ->
          let result:i32 = result in
          Spec.Utils.is_i32b 8380416 result /\
          v result % 8380417 == (v fe * v fer * 8265825) % 8380417)

val montgomery_multiply_by_constant
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (c: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      (requires Spec.Utils.is_i32b 4190208 c)
      (ensures
        fun simd_unit_future ->
          let simd_unit_future:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            simd_unit_future
          in
          Spec.Utils.is_i32b_array 8380416 simd_unit_future.f_values /\
          (forall i.
              i < 8 ==>
              (v (Seq.index simd_unit_future.f_values i) % 8380417 ==
                (v (Seq.index simd_unit.f_values i) * v c * 8265825) % 8380417)))

val montgomery_multiply (lhs rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      (requires forall i. i < 8 ==> Spec.Utils.is_i32b 4190208 (Seq.index rhs.f_values i))
      (ensures
        fun lhs_future ->
          let lhs_future:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = lhs_future in
          Spec.Utils.is_i32b_array 8380416 lhs_future.f_values /\
          (forall i.
              i < 8 ==>
              (v (Seq.index lhs_future.f_values i) % 8380417 ==
                (v (Seq.index lhs.f_values i) * v (Seq.index rhs.f_values i) * 8265825) % 8380417)))

val power2round_element (t: i32)
    : Prims.Pure (i32 & i32)
      (requires Spec.Utils.is_i32b (v Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS - 1) t)
      (ensures
        fun temp_0_ ->
          let t0, t1:(i32 & i32) = temp_0_ in
          let t0_s, t1_s = Spec.MLDSA.Math.power2round (v t) in
          v t0 == t0_s /\ v t1 == t1_s /\
          Spec.Utils.is_intb_bt (pow2 (v Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T - 1))
            (v t0))

val power2round (t0 t1: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure
      (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (requires
        Spec.Utils.is_i32b_array (v Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS - 1) t0.f_values)
      (ensures
        fun temp_0_ ->
          let t0_future, t1_future:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
            temp_0_
          in
          forall i.
            i < 8 ==>
            (let t0_v = v (Seq.index t0_future.f_values i) in
              let t0_s, t1_s = Spec.MLDSA.Math.power2round (v (Seq.index t0.f_values i)) in
              t0_v == t0_s /\ v (Seq.index t1_future.f_values i) == t1_s /\
              Spec.Utils.is_intb_bt (pow2 (v Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T - 1)
                )
                t0_v))

val infinity_norm_exceeds
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (bound: i32)
    : Prims.Pure bool
      (requires
        Spec.Utils.is_i32b_array (v Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS - 1)
          simd_unit.f_values)
      (ensures
        fun result ->
          let result:bool = result in
          result == false ==>
          (forall i. i < 8 ==> abs (v (Seq.index simd_unit.f_values i)) < v bound))

val reduce_element (fe: i32)
    : Prims.Pure i32
      (requires Spec.Utils.is_i32b 2143289343 fe)
      (ensures
        fun result ->
          let result:i32 = result in
          Spec.Utils.is_i32b 8380416 result /\ v result % 8380417 == v fe % 8380417)

val shift_left_then_reduce
      (v_SHIFT_BY: i32)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      (requires
        v v_SHIFT_BY >= 0 /\ v v_SHIFT_BY < 32 /\
        (forall i.
            i < 8 ==>
            Spec.Utils.is_i32b 2143289343 ((Seq.index simd_unit.f_values i) <<! v_SHIFT_BY)))
      (ensures
        fun simd_unit_future ->
          let simd_unit_future:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            simd_unit_future
          in
          forall i.
            i < 8 ==>
            (let fe_1 = (Seq.index simd_unit.f_values i) <<! v_SHIFT_BY in
              let fe_2 = Seq.index simd_unit_future.f_values i in
              Spec.Utils.is_i32b 8380416 fe_2 /\ v fe_2 % 8380417 == v fe_1 % 8380417))

val compute_one_hint (low high gamma2: i32)
    : Prims.Pure i32
      (requires
        v gamma2 == v Libcrux_ml_dsa.Constants.v_GAMMA2_V261_888_ \/
        v gamma2 == v Libcrux_ml_dsa.Constants.v_GAMMA2_V95_232_)
      (ensures
        fun result ->
          let result:i32 = result in
          v result = Spec.MLDSA.Math.compute_one_hint (v low) (v high) (v gamma2))

val compute_hint
      (low high: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (gamma2: i32)
      (hint: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & usize)
      (requires
        v gamma2 == v Libcrux_ml_dsa.Constants.v_GAMMA2_V261_888_ \/
        v gamma2 == v Libcrux_ml_dsa.Constants.v_GAMMA2_V95_232_)
      (ensures
        fun temp_0_ ->
          let hint_future, result:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & usize)
          =
            temp_0_
          in
          (forall i.
              i < 8 ==>
              (v (Seq.index hint_future.f_values i) =
                Spec.MLDSA.Math.compute_one_hint (v (Seq.index low.f_values i))
                  (v (Seq.index high.f_values i))
                  (v gamma2))) /\ v result == Spec.MLDSA.Math.compute_hint hint_future.f_values)

val decompose_element (gamma2 r: i32)
    : Prims.Pure (i32 & i32)
      (requires
        (v gamma2 == v Libcrux_ml_dsa.Constants.v_GAMMA2_V261_888_ \/
          v gamma2 == v Libcrux_ml_dsa.Constants.v_GAMMA2_V95_232_) /\
        Spec.Utils.is_i32b (v Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS - 1) r)
      (ensures
        fun temp_0_ ->
          let r0, r1:(i32 & i32) = temp_0_ in
          let r0_s, r1_s, cond = Spec.MLDSA.Math.decompose (v gamma2) (v r) in
          v r0 = r0_s /\ v r1 = r1_s /\
          (if cond
            then (v r0 >= - (v gamma2) /\ v r0 < 0)
            else (v r0 > - (v gamma2) /\ v r0 <= v gamma2)) /\
          (v r1 >= 0 /\ v r1 < (v Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS - 1) / (v gamma2 * 2)))

val uuse_one_hint (gamma2 r hint: i32)
    : Prims.Pure i32
      (requires
        (v gamma2 == v Libcrux_ml_dsa.Constants.v_GAMMA2_V261_888_ \/
          v gamma2 == v Libcrux_ml_dsa.Constants.v_GAMMA2_V95_232_) /\
        Spec.Utils.is_i32b (v Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS - 1) r /\
        (v hint == 0 \/ v hint == 1))
      (ensures
        fun result ->
          let result:i32 = result in
          v result == Spec.MLDSA.Math.use_one_hint (v gamma2) (v r) (v hint))

val decompose
      (gamma2: i32)
      (simd_unit low high: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure
      (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (requires
        (v gamma2 == v Libcrux_ml_dsa.Constants.v_GAMMA2_V261_888_ \/
          v gamma2 == v Libcrux_ml_dsa.Constants.v_GAMMA2_V95_232_) /\
        Spec.Utils.is_i32b_array (v Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS - 1)
          simd_unit.f_values)
      (ensures
        fun temp_0_ ->
          let low_future, high_future:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
            temp_0_
          in
          forall i.
            i < 8 ==>
            (let r = v (Seq.index simd_unit.f_values i) in
              let r0 = v (Seq.index low_future.f_values i) in
              let r1 = v (Seq.index high_future.f_values i) in
              let r0_s, r1_s, cond = Spec.MLDSA.Math.decompose (v gamma2) r in
              r0 = r0_s /\ r1 = r1_s /\
              (if cond
                then (r0 >= - (v gamma2) /\ r0 < 0)
                else (r0 > - (v gamma2) /\ r0 <= v gamma2)) /\
              (r1 >= 0 /\ r1 < (v Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS - 1) / (v gamma2 * 2)))
      )

val uuse_hint
      (gamma2: i32)
      (simd_unit hint: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      (requires
        (v gamma2 == v Libcrux_ml_dsa.Constants.v_GAMMA2_V261_888_ \/
          v gamma2 == v Libcrux_ml_dsa.Constants.v_GAMMA2_V95_232_) /\
        Spec.Utils.is_i32b_array (v Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS - 1)
          simd_unit.f_values /\
        (forall i.
            i < 8 ==> v (Seq.index hint.f_values i) == 0 \/ v (Seq.index hint.f_values i) == 1))
      (ensures
        fun hint_future ->
          let hint_future:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = hint_future in
          forall i.
            i < 8 ==>
            (let h = Seq.index hint.f_values i in
              let result = Seq.index hint_future.f_values i in
              v result =
              Spec.MLDSA.Math.use_one_hint (v gamma2) (v (Seq.index simd_unit.f_values i)) (v h)))
