module Libcrux_ml_dsa.Simd.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Hax_lib.Prop in
  ()

let v_COEFFICIENTS_IN_SIMD_UNIT: usize = mk_usize 8

let v_SIMD_UNITS_IN_RING_ELEMENT: usize =
  Libcrux_ml_dsa.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /! v_COEFFICIENTS_IN_SIMD_UNIT

let v_FIELD_MODULUS: i32 = mk_i32 8380417

let v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u64 = mk_u64 58728449

class t_Repr (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_13011033735201511749:Core.Marker.t_Copy v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9529721400157967266:Core.Clone.t_Clone v_Self;
  f_repr_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_repr_post:v_Self -> t_Array i32 (mk_usize 8) -> Type0;
  f_repr:x0: v_Self
    -> Prims.Pure (t_Array i32 (mk_usize 8)) (f_repr_pre x0) (fun result -> f_repr_post x0 result)
}

let int_is_i32 (i: Hax_lib.Int.t_Int) : bool =
  i <=
  (Hax_lib.Int.f_to_int #i32 #FStar.Tactics.Typeclasses.solve Core.Num.impl_i32__MAX
    <:
    Hax_lib.Int.t_Int) &&
  i >=
  (Hax_lib.Int.f_to_int #i32 #FStar.Tactics.Typeclasses.solve Core.Num.impl_i32__MIN
    <:
    Hax_lib.Int.t_Int)

let add_pre (lhs rhs: t_Array i32 (mk_usize 8)) : Hax_lib.Prop.t_Prop =
  Hax_lib.Prop.v_forall #usize
    #Hax_lib.Prop.t_Prop
    (fun i ->
        let i:usize = i in
        Hax_lib.Prop.implies #bool
          #bool
          (i <. v_COEFFICIENTS_IN_SIMD_UNIT <: bool)
          (int_is_i32 ((Hax_lib.Int.f_to_int #i32
                    #FStar.Tactics.Typeclasses.solve
                    (lhs.[ i ] <: i32)
                  <:
                  Hax_lib.Int.t_Int) +
                (Hax_lib.Int.f_to_int #i32 #FStar.Tactics.Typeclasses.solve (rhs.[ i ] <: i32)
                  <:
                  Hax_lib.Int.t_Int)
                <:
                Hax_lib.Int.t_Int)
            <:
            bool)
        <:
        Hax_lib.Prop.t_Prop)

let add_post (lhs rhs future_lhs: t_Array i32 (mk_usize 8)) : Hax_lib.Prop.t_Prop =
  Hax_lib.Prop.v_forall #usize
    #Hax_lib.Prop.t_Prop
    (fun i ->
        let i:usize = i in
        Hax_lib.Prop.implies #bool
          #bool
          (i <. v_COEFFICIENTS_IN_SIMD_UNIT <: bool)
          ((Hax_lib.Int.f_to_int #i32 #FStar.Tactics.Typeclasses.solve (future_lhs.[ i ] <: i32)
              <:
              Hax_lib.Int.t_Int) =
            ((Hax_lib.Int.f_to_int #i32 #FStar.Tactics.Typeclasses.solve (lhs.[ i ] <: i32)
                <:
                Hax_lib.Int.t_Int) +
              (Hax_lib.Int.f_to_int #i32 #FStar.Tactics.Typeclasses.solve (rhs.[ i ] <: i32)
                <:
                Hax_lib.Int.t_Int)
              <:
              Hax_lib.Int.t_Int)
            <:
            bool)
        <:
        Hax_lib.Prop.t_Prop)

let sub_pre (lhs rhs: t_Array i32 (mk_usize 8)) : Hax_lib.Prop.t_Prop =
  Hax_lib.Prop.v_forall #usize
    #Hax_lib.Prop.t_Prop
    (fun i ->
        let i:usize = i in
        Hax_lib.Prop.implies #bool
          #bool
          (i <. v_COEFFICIENTS_IN_SIMD_UNIT <: bool)
          (int_is_i32 ((Hax_lib.Int.f_to_int #i32
                    #FStar.Tactics.Typeclasses.solve
                    (lhs.[ i ] <: i32)
                  <:
                  Hax_lib.Int.t_Int) -
                (Hax_lib.Int.f_to_int #i32 #FStar.Tactics.Typeclasses.solve (rhs.[ i ] <: i32)
                  <:
                  Hax_lib.Int.t_Int)
                <:
                Hax_lib.Int.t_Int)
            <:
            bool)
        <:
        Hax_lib.Prop.t_Prop)

let sub_post (lhs rhs future_lhs: t_Array i32 (mk_usize 8)) : Hax_lib.Prop.t_Prop =
  Hax_lib.Prop.v_forall #usize
    #Hax_lib.Prop.t_Prop
    (fun i ->
        let i:usize = i in
        Hax_lib.Prop.implies #bool
          #bool
          (i <. v_COEFFICIENTS_IN_SIMD_UNIT <: bool)
          ((Hax_lib.Int.f_to_int #i32 #FStar.Tactics.Typeclasses.solve (future_lhs.[ i ] <: i32)
              <:
              Hax_lib.Int.t_Int) =
            ((Hax_lib.Int.f_to_int #i32 #FStar.Tactics.Typeclasses.solve (lhs.[ i ] <: i32)
                <:
                Hax_lib.Int.t_Int) -
              (Hax_lib.Int.f_to_int #i32 #FStar.Tactics.Typeclasses.solve (rhs.[ i ] <: i32)
                <:
                Hax_lib.Int.t_Int)
              <:
              Hax_lib.Int.t_Int)
            <:
            bool)
        <:
        Hax_lib.Prop.t_Prop)

class t_Operations (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_13011033735201511749:Core.Marker.t_Copy v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9529721400157967266:Core.Clone.t_Clone v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_6182285156695963586:t_Repr v_Self;
  f_zero_pre:Prims.unit -> Type0;
  f_zero_post:x: Prims.unit -> result: v_Self
    -> pred:
      Type0
        { pred ==>
          (let _:Prims.unit = x in
            (f_repr #v_Self #FStar.Tactics.Typeclasses.solve result <: t_Array i32 (mk_usize 8)) =.
            (Rust_primitives.Hax.repeat (mk_i32 0) (mk_usize 8) <: t_Array i32 (mk_usize 8))) };
  f_zero:x0: Prims.unit -> Prims.Pure v_Self (f_zero_pre x0) (fun result -> f_zero_post x0 result);
  f_from_coefficient_array_pre:array: t_Slice i32 -> out: v_Self
    -> pred:
      Type0{(Core.Slice.impl__len #i32 array <: usize) =. v_COEFFICIENTS_IN_SIMD_UNIT ==> pred};
  f_from_coefficient_array_post:array: t_Slice i32 -> out: v_Self -> out_future: v_Self
    -> pred:
      Type0
        { pred ==>
          (f_repr #v_Self #FStar.Tactics.Typeclasses.solve out_future <: t_Array i32 (mk_usize 8)) =.
          array };
  f_from_coefficient_array:x0: t_Slice i32 -> x1: v_Self
    -> Prims.Pure v_Self
        (f_from_coefficient_array_pre x0 x1)
        (fun result -> f_from_coefficient_array_post x0 x1 result);
  f_to_coefficient_array_pre:value: v_Self -> out: t_Slice i32
    -> pred: Type0{(Core.Slice.impl__len #i32 out <: usize) =. v_COEFFICIENTS_IN_SIMD_UNIT ==> pred};
  f_to_coefficient_array_post:value: v_Self -> out: t_Slice i32 -> out_future: t_Slice i32
    -> pred:
      Type0
        { pred ==>
          out_future =.
          (f_repr #v_Self #FStar.Tactics.Typeclasses.solve value <: t_Array i32 (mk_usize 8)) };
  f_to_coefficient_array:x0: v_Self -> x1: t_Slice i32
    -> Prims.Pure (t_Slice i32)
        (f_to_coefficient_array_pre x0 x1)
        (fun result -> f_to_coefficient_array_post x0 x1 result);
  f_add_pre:lhs: v_Self -> rhs: v_Self
    -> pred:
      Type0
        { add_pre (f_repr #v_Self #FStar.Tactics.Typeclasses.solve lhs <: t_Array i32 (mk_usize 8))
            (f_repr #v_Self #FStar.Tactics.Typeclasses.solve rhs <: t_Array i32 (mk_usize 8)) ==>
          pred };
  f_add_post:lhs: v_Self -> rhs: v_Self -> lhs_future: v_Self
    -> pred:
      Type0
        { pred ==>
          add_post (f_repr #v_Self #FStar.Tactics.Typeclasses.solve lhs <: t_Array i32 (mk_usize 8))
            (f_repr #v_Self #FStar.Tactics.Typeclasses.solve rhs <: t_Array i32 (mk_usize 8))
            (f_repr #v_Self #FStar.Tactics.Typeclasses.solve lhs_future <: t_Array i32 (mk_usize 8))
        };
  f_add:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self (f_add_pre x0 x1) (fun result -> f_add_post x0 x1 result);
  f_subtract_pre:lhs: v_Self -> rhs: v_Self
    -> pred:
      Type0
        { sub_pre (f_repr #v_Self #FStar.Tactics.Typeclasses.solve lhs <: t_Array i32 (mk_usize 8))
            (f_repr #v_Self #FStar.Tactics.Typeclasses.solve rhs <: t_Array i32 (mk_usize 8)) ==>
          pred };
  f_subtract_post:lhs: v_Self -> rhs: v_Self -> lhs_future: v_Self
    -> pred:
      Type0
        { pred ==>
          sub_post (f_repr #v_Self #FStar.Tactics.Typeclasses.solve lhs <: t_Array i32 (mk_usize 8))
            (f_repr #v_Self #FStar.Tactics.Typeclasses.solve rhs <: t_Array i32 (mk_usize 8))
            (f_repr #v_Self #FStar.Tactics.Typeclasses.solve lhs_future <: t_Array i32 (mk_usize 8))
        };
  f_subtract:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self (f_subtract_pre x0 x1) (fun result -> f_subtract_post x0 x1 result);
  f_infinity_norm_exceeds_pre:v_Self -> i32 -> Type0;
  f_infinity_norm_exceeds_post:v_Self -> i32 -> bool -> Type0;
  f_infinity_norm_exceeds:x0: v_Self -> x1: i32
    -> Prims.Pure bool
        (f_infinity_norm_exceeds_pre x0 x1)
        (fun result -> f_infinity_norm_exceeds_post x0 x1 result);
  f_decompose_pre:i32 -> v_Self -> v_Self -> v_Self -> Type0;
  f_decompose_post:i32 -> v_Self -> v_Self -> v_Self -> (v_Self & v_Self) -> Type0;
  f_decompose:x0: i32 -> x1: v_Self -> x2: v_Self -> x3: v_Self
    -> Prims.Pure (v_Self & v_Self)
        (f_decompose_pre x0 x1 x2 x3)
        (fun result -> f_decompose_post x0 x1 x2 x3 result);
  f_compute_hint_pre:v_Self -> v_Self -> i32 -> v_Self -> Type0;
  f_compute_hint_post:v_Self -> v_Self -> i32 -> v_Self -> (v_Self & usize) -> Type0;
  f_compute_hint:x0: v_Self -> x1: v_Self -> x2: i32 -> x3: v_Self
    -> Prims.Pure (v_Self & usize)
        (f_compute_hint_pre x0 x1 x2 x3)
        (fun result -> f_compute_hint_post x0 x1 x2 x3 result);
  f_uuse_hint_pre:i32 -> v_Self -> v_Self -> Type0;
  f_uuse_hint_post:i32 -> v_Self -> v_Self -> v_Self -> Type0;
  f_uuse_hint:x0: i32 -> x1: v_Self -> x2: v_Self
    -> Prims.Pure v_Self (f_uuse_hint_pre x0 x1 x2) (fun result -> f_uuse_hint_post x0 x1 x2 result);
  f_montgomery_multiply_pre:v_Self -> v_Self -> Type0;
  f_montgomery_multiply_post:v_Self -> v_Self -> v_Self -> Type0;
  f_montgomery_multiply:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self
        (f_montgomery_multiply_pre x0 x1)
        (fun result -> f_montgomery_multiply_post x0 x1 result);
  f_shift_left_then_reduce_pre:v_SHIFT_BY: i32 -> v_Self -> Type0;
  f_shift_left_then_reduce_post:v_SHIFT_BY: i32 -> v_Self -> v_Self -> Type0;
  f_shift_left_then_reduce:v_SHIFT_BY: i32 -> x0: v_Self
    -> Prims.Pure v_Self
        (f_shift_left_then_reduce_pre v_SHIFT_BY x0)
        (fun result -> f_shift_left_then_reduce_post v_SHIFT_BY x0 result);
  f_power2round_pre:v_Self -> v_Self -> Type0;
  f_power2round_post:v_Self -> v_Self -> (v_Self & v_Self) -> Type0;
  f_power2round:x0: v_Self -> x1: v_Self
    -> Prims.Pure (v_Self & v_Self)
        (f_power2round_pre x0 x1)
        (fun result -> f_power2round_post x0 x1 result);
  f_rejection_sample_less_than_field_modulus_pre:t_Slice u8 -> t_Slice i32 -> Type0;
  f_rejection_sample_less_than_field_modulus_post:t_Slice u8 -> t_Slice i32 -> (t_Slice i32 & usize)
    -> Type0;
  f_rejection_sample_less_than_field_modulus:x0: t_Slice u8 -> x1: t_Slice i32
    -> Prims.Pure (t_Slice i32 & usize)
        (f_rejection_sample_less_than_field_modulus_pre x0 x1)
        (fun result -> f_rejection_sample_less_than_field_modulus_post x0 x1 result);
  f_rejection_sample_less_than_eta_equals_2__pre:t_Slice u8 -> t_Slice i32 -> Type0;
  f_rejection_sample_less_than_eta_equals_2__post:t_Slice u8 -> t_Slice i32 -> (t_Slice i32 & usize)
    -> Type0;
  f_rejection_sample_less_than_eta_equals_2_:x0: t_Slice u8 -> x1: t_Slice i32
    -> Prims.Pure (t_Slice i32 & usize)
        (f_rejection_sample_less_than_eta_equals_2__pre x0 x1)
        (fun result -> f_rejection_sample_less_than_eta_equals_2__post x0 x1 result);
  f_rejection_sample_less_than_eta_equals_4__pre:t_Slice u8 -> t_Slice i32 -> Type0;
  f_rejection_sample_less_than_eta_equals_4__post:t_Slice u8 -> t_Slice i32 -> (t_Slice i32 & usize)
    -> Type0;
  f_rejection_sample_less_than_eta_equals_4_:x0: t_Slice u8 -> x1: t_Slice i32
    -> Prims.Pure (t_Slice i32 & usize)
        (f_rejection_sample_less_than_eta_equals_4__pre x0 x1)
        (fun result -> f_rejection_sample_less_than_eta_equals_4__post x0 x1 result);
  f_gamma1_serialize_pre:v_Self -> t_Slice u8 -> usize -> Type0;
  f_gamma1_serialize_post:v_Self -> t_Slice u8 -> usize -> t_Slice u8 -> Type0;
  f_gamma1_serialize:x0: v_Self -> x1: t_Slice u8 -> x2: usize
    -> Prims.Pure (t_Slice u8)
        (f_gamma1_serialize_pre x0 x1 x2)
        (fun result -> f_gamma1_serialize_post x0 x1 x2 result);
  f_gamma1_deserialize_pre:t_Slice u8 -> v_Self -> usize -> Type0;
  f_gamma1_deserialize_post:t_Slice u8 -> v_Self -> usize -> v_Self -> Type0;
  f_gamma1_deserialize:x0: t_Slice u8 -> x1: v_Self -> x2: usize
    -> Prims.Pure v_Self
        (f_gamma1_deserialize_pre x0 x1 x2)
        (fun result -> f_gamma1_deserialize_post x0 x1 x2 result);
  f_commitment_serialize_pre:simd_unit: v_Self -> serialized: t_Slice u8
    -> pred:
      Type0
        { (Core.Slice.impl__len #u8 serialized <: usize) =. mk_usize 4 ||
          (Core.Slice.impl__len #u8 serialized <: usize) =. mk_usize 6 ==>
          pred };
  f_commitment_serialize_post:
      simd_unit: v_Self ->
      serialized: t_Slice u8 ->
      serialized_future: t_Slice u8
    -> pred:
      Type0
        { pred ==>
          (Core.Slice.impl__len #u8 serialized_future <: usize) =.
          (Core.Slice.impl__len #u8 serialized <: usize) };
  f_commitment_serialize:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure (t_Slice u8)
        (f_commitment_serialize_pre x0 x1)
        (fun result -> f_commitment_serialize_post x0 x1 result);
  f_error_serialize_pre:Libcrux_ml_dsa.Constants.t_Eta -> v_Self -> t_Slice u8 -> Type0;
  f_error_serialize_post:Libcrux_ml_dsa.Constants.t_Eta -> v_Self -> t_Slice u8 -> t_Slice u8
    -> Type0;
  f_error_serialize:x0: Libcrux_ml_dsa.Constants.t_Eta -> x1: v_Self -> x2: t_Slice u8
    -> Prims.Pure (t_Slice u8)
        (f_error_serialize_pre x0 x1 x2)
        (fun result -> f_error_serialize_post x0 x1 x2 result);
  f_error_deserialize_pre:Libcrux_ml_dsa.Constants.t_Eta -> t_Slice u8 -> v_Self -> Type0;
  f_error_deserialize_post:Libcrux_ml_dsa.Constants.t_Eta -> t_Slice u8 -> v_Self -> v_Self -> Type0;
  f_error_deserialize:x0: Libcrux_ml_dsa.Constants.t_Eta -> x1: t_Slice u8 -> x2: v_Self
    -> Prims.Pure v_Self
        (f_error_deserialize_pre x0 x1 x2)
        (fun result -> f_error_deserialize_post x0 x1 x2 result);
  f_t0_serialize_pre:v_Self -> t_Slice u8 -> Type0;
  f_t0_serialize_post:v_Self -> t_Slice u8 -> t_Slice u8 -> Type0;
  f_t0_serialize:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure (t_Slice u8)
        (f_t0_serialize_pre x0 x1)
        (fun result -> f_t0_serialize_post x0 x1 result);
  f_t0_deserialize_pre:t_Slice u8 -> v_Self -> Type0;
  f_t0_deserialize_post:t_Slice u8 -> v_Self -> v_Self -> Type0;
  f_t0_deserialize:x0: t_Slice u8 -> x1: v_Self
    -> Prims.Pure v_Self
        (f_t0_deserialize_pre x0 x1)
        (fun result -> f_t0_deserialize_post x0 x1 result);
  f_t1_serialize_pre:v_Self -> t_Slice u8 -> Type0;
  f_t1_serialize_post:v_Self -> t_Slice u8 -> t_Slice u8 -> Type0;
  f_t1_serialize:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure (t_Slice u8)
        (f_t1_serialize_pre x0 x1)
        (fun result -> f_t1_serialize_post x0 x1 result);
  f_t1_deserialize_pre:t_Slice u8 -> v_Self -> Type0;
  f_t1_deserialize_post:t_Slice u8 -> v_Self -> v_Self -> Type0;
  f_t1_deserialize:x0: t_Slice u8 -> x1: v_Self
    -> Prims.Pure v_Self
        (f_t1_deserialize_pre x0 x1)
        (fun result -> f_t1_deserialize_post x0 x1 result);
  f_ntt_pre:t_Array v_Self (mk_usize 32) -> Type0;
  f_ntt_post:t_Array v_Self (mk_usize 32) -> t_Array v_Self (mk_usize 32) -> Type0;
  f_ntt:x0: t_Array v_Self (mk_usize 32)
    -> Prims.Pure (t_Array v_Self (mk_usize 32)) (f_ntt_pre x0) (fun result -> f_ntt_post x0 result);
  f_invert_ntt_montgomery_pre:t_Array v_Self (mk_usize 32) -> Type0;
  f_invert_ntt_montgomery_post:t_Array v_Self (mk_usize 32) -> t_Array v_Self (mk_usize 32) -> Type0;
  f_invert_ntt_montgomery:x0: t_Array v_Self (mk_usize 32)
    -> Prims.Pure (t_Array v_Self (mk_usize 32))
        (f_invert_ntt_montgomery_pre x0)
        (fun result -> f_invert_ntt_montgomery_post x0 result)
}
