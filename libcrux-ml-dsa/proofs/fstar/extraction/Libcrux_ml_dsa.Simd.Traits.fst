module Libcrux_ml_dsa.Simd.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_Operations (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_11581440318597584651:Core.Marker.t_Copy v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9442900250278684536:Core.Clone.t_Clone v_Self;
  f_ZERO_pre:Prims.unit -> Type0;
  f_ZERO_post:Prims.unit -> v_Self -> Type0;
  f_ZERO:x0: Prims.unit -> Prims.Pure v_Self (f_ZERO_pre x0) (fun result -> f_ZERO_post x0 result);
  f_from_coefficient_array_pre:t_Slice i32 -> Type0;
  f_from_coefficient_array_post:t_Slice i32 -> v_Self -> Type0;
  f_from_coefficient_array:x0: t_Slice i32
    -> Prims.Pure v_Self
        (f_from_coefficient_array_pre x0)
        (fun result -> f_from_coefficient_array_post x0 result);
  f_to_coefficient_array_pre:v_Self -> Type0;
  f_to_coefficient_array_post:v_Self -> t_Array i32 (Rust_primitives.mk_usize 8) -> Type0;
  f_to_coefficient_array:x0: v_Self
    -> Prims.Pure (t_Array i32 (Rust_primitives.mk_usize 8))
        (f_to_coefficient_array_pre x0)
        (fun result -> f_to_coefficient_array_post x0 result);
  f_add_pre:v_Self -> v_Self -> Type0;
  f_add_post:v_Self -> v_Self -> v_Self -> Type0;
  f_add:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self (f_add_pre x0 x1) (fun result -> f_add_post x0 x1 result);
  f_subtract_pre:v_Self -> v_Self -> Type0;
  f_subtract_post:v_Self -> v_Self -> v_Self -> Type0;
  f_subtract:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self (f_subtract_pre x0 x1) (fun result -> f_subtract_post x0 x1 result);
  f_infinity_norm_exceeds_pre:v_Self -> i32 -> Type0;
  f_infinity_norm_exceeds_post:v_Self -> i32 -> bool -> Type0;
  f_infinity_norm_exceeds:x0: v_Self -> x1: i32
    -> Prims.Pure bool
        (f_infinity_norm_exceeds_pre x0 x1)
        (fun result -> f_infinity_norm_exceeds_post x0 x1 result);
  f_decompose_pre:v_GAMMA2: i32 -> v_Self -> Type0;
  f_decompose_post:v_GAMMA2: i32 -> v_Self -> (v_Self & v_Self) -> Type0;
  f_decompose:v_GAMMA2: i32 -> x0: v_Self
    -> Prims.Pure (v_Self & v_Self)
        (f_decompose_pre v_GAMMA2 x0)
        (fun result -> f_decompose_post v_GAMMA2 x0 result);
  f_compute_hint_pre:v_GAMMA2: i32 -> v_Self -> v_Self -> Type0;
  f_compute_hint_post:v_GAMMA2: i32 -> v_Self -> v_Self -> (usize & v_Self) -> Type0;
  f_compute_hint:v_GAMMA2: i32 -> x0: v_Self -> x1: v_Self
    -> Prims.Pure (usize & v_Self)
        (f_compute_hint_pre v_GAMMA2 x0 x1)
        (fun result -> f_compute_hint_post v_GAMMA2 x0 x1 result);
  f_use_hint_pre:v_GAMMA2: i32 -> v_Self -> v_Self -> Type0;
  f_use_hint_post:v_GAMMA2: i32 -> v_Self -> v_Self -> v_Self -> Type0;
  f_use_hint:v_GAMMA2: i32 -> x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self
        (f_use_hint_pre v_GAMMA2 x0 x1)
        (fun result -> f_use_hint_post v_GAMMA2 x0 x1 result);
  f_montgomery_multiply_pre:v_Self -> v_Self -> Type0;
  f_montgomery_multiply_post:v_Self -> v_Self -> v_Self -> Type0;
  f_montgomery_multiply:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self
        (f_montgomery_multiply_pre x0 x1)
        (fun result -> f_montgomery_multiply_post x0 x1 result);
  f_montgomery_multiply_by_constant_pre:v_Self -> i32 -> Type0;
  f_montgomery_multiply_by_constant_post:v_Self -> i32 -> v_Self -> Type0;
  f_montgomery_multiply_by_constant:x0: v_Self -> x1: i32
    -> Prims.Pure v_Self
        (f_montgomery_multiply_by_constant_pre x0 x1)
        (fun result -> f_montgomery_multiply_by_constant_post x0 x1 result);
  f_shift_left_then_reduce_pre:v_SHIFT_BY: i32 -> v_Self -> Type0;
  f_shift_left_then_reduce_post:v_SHIFT_BY: i32 -> v_Self -> v_Self -> Type0;
  f_shift_left_then_reduce:v_SHIFT_BY: i32 -> x0: v_Self
    -> Prims.Pure v_Self
        (f_shift_left_then_reduce_pre v_SHIFT_BY x0)
        (fun result -> f_shift_left_then_reduce_post v_SHIFT_BY x0 result);
  f_power2round_pre:v_Self -> Type0;
  f_power2round_post:v_Self -> (v_Self & v_Self) -> Type0;
  f_power2round:x0: v_Self
    -> Prims.Pure (v_Self & v_Self)
        (f_power2round_pre x0)
        (fun result -> f_power2round_post x0 result);
  f_rejection_sample_less_than_field_modulus_pre:t_Slice u8 -> t_Slice i32 -> Type0;
  f_rejection_sample_less_than_field_modulus_post:t_Slice u8 -> t_Slice i32 -> (t_Slice i32 & usize)
    -> Type0;
  f_rejection_sample_less_than_field_modulus:x0: t_Slice u8 -> x1: t_Slice i32
    -> Prims.Pure (t_Slice i32 & usize)
        (f_rejection_sample_less_than_field_modulus_pre x0 x1)
        (fun result -> f_rejection_sample_less_than_field_modulus_post x0 x1 result);
  f_rejection_sample_less_than_eta_equals_2_pre:t_Slice u8 -> t_Slice i32 -> Type0;
  f_rejection_sample_less_than_eta_equals_2_post:t_Slice u8 -> t_Slice i32 -> (t_Slice i32 & usize)
    -> Type0;
  f_rejection_sample_less_than_eta_equals_2_:x0: t_Slice u8 -> x1: t_Slice i32
    -> Prims.Pure (t_Slice i32 & usize)
        (f_rejection_sample_less_than_eta_equals_2_pre x0 x1)
        (fun result -> f_rejection_sample_less_than_eta_equals_2_post x0 x1 result);
  f_rejection_sample_less_than_eta_equals_4_pre:t_Slice u8 -> t_Slice i32 -> Type0;
  f_rejection_sample_less_than_eta_equals_4_post:t_Slice u8 -> t_Slice i32 -> (t_Slice i32 & usize)
    -> Type0;
  f_rejection_sample_less_than_eta_equals_4_:x0: t_Slice u8 -> x1: t_Slice i32
    -> Prims.Pure (t_Slice i32 & usize)
        (f_rejection_sample_less_than_eta_equals_4_pre x0 x1)
        (fun result -> f_rejection_sample_less_than_eta_equals_4_post x0 x1 result);
  f_gamma1_serialize_pre:v_OUTPUT_SIZE: usize -> v_Self -> Type0;
  f_gamma1_serialize_post:v_OUTPUT_SIZE: usize -> v_Self -> t_Array u8 v_OUTPUT_SIZE -> Type0;
  f_gamma1_serialize:v_OUTPUT_SIZE: usize -> x0: v_Self
    -> Prims.Pure (t_Array u8 v_OUTPUT_SIZE)
        (f_gamma1_serialize_pre v_OUTPUT_SIZE x0)
        (fun result -> f_gamma1_serialize_post v_OUTPUT_SIZE x0 result);
  f_gamma1_deserialize_pre:v_GAMMA1_EXPONENT: usize -> t_Slice u8 -> Type0;
  f_gamma1_deserialize_post:v_GAMMA1_EXPONENT: usize -> t_Slice u8 -> v_Self -> Type0;
  f_gamma1_deserialize:v_GAMMA1_EXPONENT: usize -> x0: t_Slice u8
    -> Prims.Pure v_Self
        (f_gamma1_deserialize_pre v_GAMMA1_EXPONENT x0)
        (fun result -> f_gamma1_deserialize_post v_GAMMA1_EXPONENT x0 result);
  f_commitment_serialize_pre:v_OUTPUT_SIZE: usize -> v_Self -> Type0;
  f_commitment_serialize_post:v_OUTPUT_SIZE: usize -> v_Self -> t_Array u8 v_OUTPUT_SIZE -> Type0;
  f_commitment_serialize:v_OUTPUT_SIZE: usize -> x0: v_Self
    -> Prims.Pure (t_Array u8 v_OUTPUT_SIZE)
        (f_commitment_serialize_pre v_OUTPUT_SIZE x0)
        (fun result -> f_commitment_serialize_post v_OUTPUT_SIZE x0 result);
  f_error_serialize_pre:v_OUTPUT_SIZE: usize -> v_Self -> Type0;
  f_error_serialize_post:v_OUTPUT_SIZE: usize -> v_Self -> t_Array u8 v_OUTPUT_SIZE -> Type0;
  f_error_serialize:v_OUTPUT_SIZE: usize -> x0: v_Self
    -> Prims.Pure (t_Array u8 v_OUTPUT_SIZE)
        (f_error_serialize_pre v_OUTPUT_SIZE x0)
        (fun result -> f_error_serialize_post v_OUTPUT_SIZE x0 result);
  f_error_deserialize_pre:v_ETA: usize -> t_Slice u8 -> Type0;
  f_error_deserialize_post:v_ETA: usize -> t_Slice u8 -> v_Self -> Type0;
  f_error_deserialize:v_ETA: usize -> x0: t_Slice u8
    -> Prims.Pure v_Self
        (f_error_deserialize_pre v_ETA x0)
        (fun result -> f_error_deserialize_post v_ETA x0 result);
  f_t0_serialize_pre:v_Self -> Type0;
  f_t0_serialize_post:v_Self -> t_Array u8 (Rust_primitives.mk_usize 13) -> Type0;
  f_t0_serialize:x0: v_Self
    -> Prims.Pure (t_Array u8 (Rust_primitives.mk_usize 13))
        (f_t0_serialize_pre x0)
        (fun result -> f_t0_serialize_post x0 result);
  f_t0_deserialize_pre:t_Slice u8 -> Type0;
  f_t0_deserialize_post:t_Slice u8 -> v_Self -> Type0;
  f_t0_deserialize:x0: t_Slice u8
    -> Prims.Pure v_Self (f_t0_deserialize_pre x0) (fun result -> f_t0_deserialize_post x0 result);
  f_t1_serialize_pre:v_Self -> Type0;
  f_t1_serialize_post:v_Self -> t_Array u8 (Rust_primitives.mk_usize 10) -> Type0;
  f_t1_serialize:x0: v_Self
    -> Prims.Pure (t_Array u8 (Rust_primitives.mk_usize 10))
        (f_t1_serialize_pre x0)
        (fun result -> f_t1_serialize_post x0 result);
  f_t1_deserialize_pre:t_Slice u8 -> Type0;
  f_t1_deserialize_post:t_Slice u8 -> v_Self -> Type0;
  f_t1_deserialize:x0: t_Slice u8
    -> Prims.Pure v_Self (f_t1_deserialize_pre x0) (fun result -> f_t1_deserialize_post x0 result);
  f_ntt_pre:t_Array v_Self (Rust_primitives.mk_usize 32) -> Type0;
  f_ntt_post:
      t_Array v_Self (Rust_primitives.mk_usize 32) ->
      t_Array v_Self (Rust_primitives.mk_usize 32)
    -> Type0;
  f_ntt:x0: t_Array v_Self (Rust_primitives.mk_usize 32)
    -> Prims.Pure (t_Array v_Self (Rust_primitives.mk_usize 32))
        (f_ntt_pre x0)
        (fun result -> f_ntt_post x0 result);
  f_invert_ntt_at_layer_0_pre:v_Self -> i32 -> i32 -> i32 -> i32 -> Type0;
  f_invert_ntt_at_layer_0_post:v_Self -> i32 -> i32 -> i32 -> i32 -> v_Self -> Type0;
  f_invert_ntt_at_layer_0_:x0: v_Self -> x1: i32 -> x2: i32 -> x3: i32 -> x4: i32
    -> Prims.Pure v_Self
        (f_invert_ntt_at_layer_0_pre x0 x1 x2 x3 x4)
        (fun result -> f_invert_ntt_at_layer_0_post x0 x1 x2 x3 x4 result);
  f_invert_ntt_at_layer_1_pre:v_Self -> i32 -> i32 -> Type0;
  f_invert_ntt_at_layer_1_post:v_Self -> i32 -> i32 -> v_Self -> Type0;
  f_invert_ntt_at_layer_1_:x0: v_Self -> x1: i32 -> x2: i32
    -> Prims.Pure v_Self
        (f_invert_ntt_at_layer_1_pre x0 x1 x2)
        (fun result -> f_invert_ntt_at_layer_1_post x0 x1 x2 result);
  f_invert_ntt_at_layer_2_pre:v_Self -> i32 -> Type0;
  f_invert_ntt_at_layer_2_post:v_Self -> i32 -> v_Self -> Type0;
  f_invert_ntt_at_layer_2_:x0: v_Self -> x1: i32
    -> Prims.Pure v_Self
        (f_invert_ntt_at_layer_2_pre x0 x1)
        (fun result -> f_invert_ntt_at_layer_2_post x0 x1 result)
}

let v_COEFFICIENTS_IN_SIMD_UNIT: usize = Rust_primitives.mk_usize 8

let v_FIELD_MODULUS: i32 = Rust_primitives.mk_i32 8380417

let v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u64 = Rust_primitives.mk_u64 58728449

let v_SIMD_UNITS_IN_RING_ELEMENT: usize =
  Libcrux_ml_dsa.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /! v_COEFFICIENTS_IN_SIMD_UNIT

let v_ZETAS_TIMES_MONTGOMERY_R: t_Array i32 (Rust_primitives.mk_usize 256) =
  let list =
    [
      Rust_primitives.mk_i32 0; Rust_primitives.mk_i32 25847; Rust_primitives.mk_i32 (-2608894);
      Rust_primitives.mk_i32 (-518909); Rust_primitives.mk_i32 237124;
      Rust_primitives.mk_i32 (-777960); Rust_primitives.mk_i32 (-876248);
      Rust_primitives.mk_i32 466468; Rust_primitives.mk_i32 1826347; Rust_primitives.mk_i32 2353451;
      Rust_primitives.mk_i32 (-359251); Rust_primitives.mk_i32 (-2091905);
      Rust_primitives.mk_i32 3119733; Rust_primitives.mk_i32 (-2884855);
      Rust_primitives.mk_i32 3111497; Rust_primitives.mk_i32 2680103; Rust_primitives.mk_i32 2725464;
      Rust_primitives.mk_i32 1024112; Rust_primitives.mk_i32 (-1079900);
      Rust_primitives.mk_i32 3585928; Rust_primitives.mk_i32 (-549488);
      Rust_primitives.mk_i32 (-1119584); Rust_primitives.mk_i32 2619752;
      Rust_primitives.mk_i32 (-2108549); Rust_primitives.mk_i32 (-2118186);
      Rust_primitives.mk_i32 (-3859737); Rust_primitives.mk_i32 (-1399561);
      Rust_primitives.mk_i32 (-3277672); Rust_primitives.mk_i32 1757237;
      Rust_primitives.mk_i32 (-19422); Rust_primitives.mk_i32 4010497; Rust_primitives.mk_i32 280005;
      Rust_primitives.mk_i32 2706023; Rust_primitives.mk_i32 95776; Rust_primitives.mk_i32 3077325;
      Rust_primitives.mk_i32 3530437; Rust_primitives.mk_i32 (-1661693);
      Rust_primitives.mk_i32 (-3592148); Rust_primitives.mk_i32 (-2537516);
      Rust_primitives.mk_i32 3915439; Rust_primitives.mk_i32 (-3861115);
      Rust_primitives.mk_i32 (-3043716); Rust_primitives.mk_i32 3574422;
      Rust_primitives.mk_i32 (-2867647); Rust_primitives.mk_i32 3539968;
      Rust_primitives.mk_i32 (-300467); Rust_primitives.mk_i32 2348700;
      Rust_primitives.mk_i32 (-539299); Rust_primitives.mk_i32 (-1699267);
      Rust_primitives.mk_i32 (-1643818); Rust_primitives.mk_i32 3505694;
      Rust_primitives.mk_i32 (-3821735); Rust_primitives.mk_i32 3507263;
      Rust_primitives.mk_i32 (-2140649); Rust_primitives.mk_i32 (-1600420);
      Rust_primitives.mk_i32 3699596; Rust_primitives.mk_i32 811944; Rust_primitives.mk_i32 531354;
      Rust_primitives.mk_i32 954230; Rust_primitives.mk_i32 3881043; Rust_primitives.mk_i32 3900724;
      Rust_primitives.mk_i32 (-2556880); Rust_primitives.mk_i32 2071892;
      Rust_primitives.mk_i32 (-2797779); Rust_primitives.mk_i32 (-3930395);
      Rust_primitives.mk_i32 (-1528703); Rust_primitives.mk_i32 (-3677745);
      Rust_primitives.mk_i32 (-3041255); Rust_primitives.mk_i32 (-1452451);
      Rust_primitives.mk_i32 3475950; Rust_primitives.mk_i32 2176455;
      Rust_primitives.mk_i32 (-1585221); Rust_primitives.mk_i32 (-1257611);
      Rust_primitives.mk_i32 1939314; Rust_primitives.mk_i32 (-4083598);
      Rust_primitives.mk_i32 (-1000202); Rust_primitives.mk_i32 (-3190144);
      Rust_primitives.mk_i32 (-3157330); Rust_primitives.mk_i32 (-3632928);
      Rust_primitives.mk_i32 126922; Rust_primitives.mk_i32 3412210;
      Rust_primitives.mk_i32 (-983419); Rust_primitives.mk_i32 2147896;
      Rust_primitives.mk_i32 2715295; Rust_primitives.mk_i32 (-2967645);
      Rust_primitives.mk_i32 (-3693493); Rust_primitives.mk_i32 (-411027);
      Rust_primitives.mk_i32 (-2477047); Rust_primitives.mk_i32 (-671102);
      Rust_primitives.mk_i32 (-1228525); Rust_primitives.mk_i32 (-22981);
      Rust_primitives.mk_i32 (-1308169); Rust_primitives.mk_i32 (-381987);
      Rust_primitives.mk_i32 1349076; Rust_primitives.mk_i32 1852771;
      Rust_primitives.mk_i32 (-1430430); Rust_primitives.mk_i32 (-3343383);
      Rust_primitives.mk_i32 264944; Rust_primitives.mk_i32 508951; Rust_primitives.mk_i32 3097992;
      Rust_primitives.mk_i32 44288; Rust_primitives.mk_i32 (-1100098); Rust_primitives.mk_i32 904516;
      Rust_primitives.mk_i32 3958618; Rust_primitives.mk_i32 (-3724342);
      Rust_primitives.mk_i32 (-8578); Rust_primitives.mk_i32 1653064;
      Rust_primitives.mk_i32 (-3249728); Rust_primitives.mk_i32 2389356;
      Rust_primitives.mk_i32 (-210977); Rust_primitives.mk_i32 759969;
      Rust_primitives.mk_i32 (-1316856); Rust_primitives.mk_i32 189548;
      Rust_primitives.mk_i32 (-3553272); Rust_primitives.mk_i32 3159746;
      Rust_primitives.mk_i32 (-1851402); Rust_primitives.mk_i32 (-2409325);
      Rust_primitives.mk_i32 (-177440); Rust_primitives.mk_i32 1315589;
      Rust_primitives.mk_i32 1341330; Rust_primitives.mk_i32 1285669;
      Rust_primitives.mk_i32 (-1584928); Rust_primitives.mk_i32 (-812732);
      Rust_primitives.mk_i32 (-1439742); Rust_primitives.mk_i32 (-3019102);
      Rust_primitives.mk_i32 (-3881060); Rust_primitives.mk_i32 (-3628969);
      Rust_primitives.mk_i32 3839961; Rust_primitives.mk_i32 2091667; Rust_primitives.mk_i32 3407706;
      Rust_primitives.mk_i32 2316500; Rust_primitives.mk_i32 3817976;
      Rust_primitives.mk_i32 (-3342478); Rust_primitives.mk_i32 2244091;
      Rust_primitives.mk_i32 (-2446433); Rust_primitives.mk_i32 (-3562462);
      Rust_primitives.mk_i32 266997; Rust_primitives.mk_i32 2434439;
      Rust_primitives.mk_i32 (-1235728); Rust_primitives.mk_i32 3513181;
      Rust_primitives.mk_i32 (-3520352); Rust_primitives.mk_i32 (-3759364);
      Rust_primitives.mk_i32 (-1197226); Rust_primitives.mk_i32 (-3193378);
      Rust_primitives.mk_i32 900702; Rust_primitives.mk_i32 1859098; Rust_primitives.mk_i32 909542;
      Rust_primitives.mk_i32 819034; Rust_primitives.mk_i32 495491;
      Rust_primitives.mk_i32 (-1613174); Rust_primitives.mk_i32 (-43260);
      Rust_primitives.mk_i32 (-522500); Rust_primitives.mk_i32 (-655327);
      Rust_primitives.mk_i32 (-3122442); Rust_primitives.mk_i32 2031748;
      Rust_primitives.mk_i32 3207046; Rust_primitives.mk_i32 (-3556995);
      Rust_primitives.mk_i32 (-525098); Rust_primitives.mk_i32 (-768622);
      Rust_primitives.mk_i32 (-3595838); Rust_primitives.mk_i32 342297;
      Rust_primitives.mk_i32 286988; Rust_primitives.mk_i32 (-2437823);
      Rust_primitives.mk_i32 4108315; Rust_primitives.mk_i32 3437287;
      Rust_primitives.mk_i32 (-3342277); Rust_primitives.mk_i32 1735879;
      Rust_primitives.mk_i32 203044; Rust_primitives.mk_i32 2842341; Rust_primitives.mk_i32 2691481;
      Rust_primitives.mk_i32 (-2590150); Rust_primitives.mk_i32 1265009;
      Rust_primitives.mk_i32 4055324; Rust_primitives.mk_i32 1247620; Rust_primitives.mk_i32 2486353;
      Rust_primitives.mk_i32 1595974; Rust_primitives.mk_i32 (-3767016);
      Rust_primitives.mk_i32 1250494; Rust_primitives.mk_i32 2635921;
      Rust_primitives.mk_i32 (-3548272); Rust_primitives.mk_i32 (-2994039);
      Rust_primitives.mk_i32 1869119; Rust_primitives.mk_i32 1903435;
      Rust_primitives.mk_i32 (-1050970); Rust_primitives.mk_i32 (-1333058);
      Rust_primitives.mk_i32 1237275; Rust_primitives.mk_i32 (-3318210);
      Rust_primitives.mk_i32 (-1430225); Rust_primitives.mk_i32 (-451100);
      Rust_primitives.mk_i32 1312455; Rust_primitives.mk_i32 3306115;
      Rust_primitives.mk_i32 (-1962642); Rust_primitives.mk_i32 (-1279661);
      Rust_primitives.mk_i32 1917081; Rust_primitives.mk_i32 (-2546312);
      Rust_primitives.mk_i32 (-1374803); Rust_primitives.mk_i32 1500165;
      Rust_primitives.mk_i32 777191; Rust_primitives.mk_i32 2235880; Rust_primitives.mk_i32 3406031;
      Rust_primitives.mk_i32 (-542412); Rust_primitives.mk_i32 (-2831860);
      Rust_primitives.mk_i32 (-1671176); Rust_primitives.mk_i32 (-1846953);
      Rust_primitives.mk_i32 (-2584293); Rust_primitives.mk_i32 (-3724270);
      Rust_primitives.mk_i32 594136; Rust_primitives.mk_i32 (-3776993);
      Rust_primitives.mk_i32 (-2013608); Rust_primitives.mk_i32 2432395;
      Rust_primitives.mk_i32 2454455; Rust_primitives.mk_i32 (-164721);
      Rust_primitives.mk_i32 1957272; Rust_primitives.mk_i32 3369112; Rust_primitives.mk_i32 185531;
      Rust_primitives.mk_i32 (-1207385); Rust_primitives.mk_i32 (-3183426);
      Rust_primitives.mk_i32 162844; Rust_primitives.mk_i32 1616392; Rust_primitives.mk_i32 3014001;
      Rust_primitives.mk_i32 810149; Rust_primitives.mk_i32 1652634;
      Rust_primitives.mk_i32 (-3694233); Rust_primitives.mk_i32 (-1799107);
      Rust_primitives.mk_i32 (-3038916); Rust_primitives.mk_i32 3523897;
      Rust_primitives.mk_i32 3866901; Rust_primitives.mk_i32 269760; Rust_primitives.mk_i32 2213111;
      Rust_primitives.mk_i32 (-975884); Rust_primitives.mk_i32 1717735;
      Rust_primitives.mk_i32 472078; Rust_primitives.mk_i32 (-426683);
      Rust_primitives.mk_i32 1723600; Rust_primitives.mk_i32 (-1803090);
      Rust_primitives.mk_i32 1910376; Rust_primitives.mk_i32 (-1667432);
      Rust_primitives.mk_i32 (-1104333); Rust_primitives.mk_i32 (-260646);
      Rust_primitives.mk_i32 (-3833893); Rust_primitives.mk_i32 (-2939036);
      Rust_primitives.mk_i32 (-2235985); Rust_primitives.mk_i32 (-420899);
      Rust_primitives.mk_i32 (-2286327); Rust_primitives.mk_i32 183443;
      Rust_primitives.mk_i32 (-976891); Rust_primitives.mk_i32 1612842;
      Rust_primitives.mk_i32 (-3545687); Rust_primitives.mk_i32 (-554416);
      Rust_primitives.mk_i32 3919660; Rust_primitives.mk_i32 (-48306);
      Rust_primitives.mk_i32 (-1362209); Rust_primitives.mk_i32 3937738;
      Rust_primitives.mk_i32 1400424; Rust_primitives.mk_i32 (-846154);
      Rust_primitives.mk_i32 1976782
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 256);
  Rust_primitives.Hax.array_of_list 256 list

let montgomery_multiply_by_fer
      (#v_S: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Operations v_S)
      (simd_unit: v_S)
      (fer: i32)
    : v_S = f_montgomery_multiply_by_constant #v_S #FStar.Tactics.Typeclasses.solve simd_unit fer
