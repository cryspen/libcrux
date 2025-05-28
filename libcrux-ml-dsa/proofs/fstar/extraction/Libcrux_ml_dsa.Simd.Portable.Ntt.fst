module Libcrux_ml_dsa.Simd.Portable.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Portable.Vector_type in
  ()

let v_NTT_BASE_BOUND: u32 = Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MID

#push-options "--z3rlimit 300 --split_queries always"

let simd_layer_factor (step:usize) =
    match step with
    | MkInt 1 -> 7
    | MkInt 2 -> 6
    | MkInt 4 -> 5
    | _ -> 5

[@@ "opaque_to_smt"]

let simd_unit_ntt_step
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (zeta: i32)
      (index step: usize)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      (requires
        v step <= 4 /\ v index + v step < 8 /\
        Spec.Utils.is_i32b (v v_NTT_BASE_BOUND +
            (simd_layer_factor step * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX))
          (Seq.index simd_unit.f_values (v index)) /\
        Spec.Utils.is_i32b (v v_NTT_BASE_BOUND +
            (simd_layer_factor step * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX))
          (Seq.index simd_unit.f_values (v index + v step)) /\ Spec.Utils.is_i32b 4190208 zeta)
      (ensures
        fun simd_unit_future ->
          let simd_unit_future:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            simd_unit_future
          in
          Spec.Utils.modifies2_8 simd_unit.f_values simd_unit_future.f_values index (index +! step) /\
          Spec.Utils.is_i32b (v v_NTT_BASE_BOUND +
              ((simd_layer_factor step + 1) * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX))
            (Seq.index simd_unit_future.f_values (v index)) /\
          Spec.Utils.is_i32b (v v_NTT_BASE_BOUND +
              ((simd_layer_factor step + 1) * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX))
            (Seq.index simd_unit_future.f_values (v index + v step))) =
  let t:i32 =
    Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_fe_by_fer (simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ index +! step <: usize ]
        <:
        i32)
      zeta
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        (index +! step <: usize)
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ index ] <: i32) -! t <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    {
      simd_unit with
      Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
          .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
        index
        ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ index ] <: i32) +! t <: i32)
    }
    <:
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  in
  simd_unit

#pop-options

#push-options "--z3rlimit 300 --split_queries always"

[@@ "opaque_to_smt"]

let simd_unit_ntt_at_layer_0_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (zeta0 zeta1 zeta2 zeta3: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      (requires
        Spec.Utils.is_i32b_array (v v_NTT_BASE_BOUND +
            7 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
          simd_unit.f_values /\ Spec.Utils.is_i32b 4190208 zeta0 /\ Spec.Utils.is_i32b 4190208 zeta1 /\
        Spec.Utils.is_i32b 4190208 zeta2 /\ Spec.Utils.is_i32b 4190208 zeta3)
      (ensures
        fun simd_unit_future ->
          let simd_unit_future:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            simd_unit_future
          in
          Spec.Utils.is_i32b_array (v v_NTT_BASE_BOUND +
              8 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
            simd_unit_future.f_values) =
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    simd_unit_ntt_step simd_unit zeta0 (mk_usize 0) (mk_usize 1)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    simd_unit_ntt_step simd_unit zeta1 (mk_usize 2) (mk_usize 1)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    simd_unit_ntt_step simd_unit zeta2 (mk_usize 4) (mk_usize 1)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    simd_unit_ntt_step simd_unit zeta3 (mk_usize 6) (mk_usize 1)
  in
  simd_unit

#pop-options

#push-options "--z3rlimit 300 --split_queries always"

[@@ "opaque_to_smt"]

let simd_unit_ntt_at_layer_1_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (zeta1 zeta2: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      (requires
        Spec.Utils.is_i32b_array (v v_NTT_BASE_BOUND +
            6 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
          simd_unit.f_values /\ Spec.Utils.is_i32b 4190208 zeta1 /\ Spec.Utils.is_i32b 4190208 zeta2
      )
      (ensures
        fun simd_unit_future ->
          let simd_unit_future:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            simd_unit_future
          in
          Spec.Utils.is_i32b_array (v v_NTT_BASE_BOUND +
              7 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
            simd_unit_future.f_values) =
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    simd_unit_ntt_step simd_unit zeta1 (mk_usize 0) (mk_usize 2)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    simd_unit_ntt_step simd_unit zeta1 (mk_usize 1) (mk_usize 2)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    simd_unit_ntt_step simd_unit zeta2 (mk_usize 4) (mk_usize 2)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    simd_unit_ntt_step simd_unit zeta2 (mk_usize 5) (mk_usize 2)
  in
  simd_unit

#pop-options

#push-options "--z3rlimit 300 --split_queries always"

[@@ "opaque_to_smt"]

let simd_unit_ntt_at_layer_2_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (zeta: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      (requires
        Spec.Utils.is_i32b_array (v v_NTT_BASE_BOUND +
            5 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
          simd_unit.f_values /\ Spec.Utils.is_i32b 4190208 zeta)
      (ensures
        fun simd_unit_future ->
          let simd_unit_future:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            simd_unit_future
          in
          Spec.Utils.is_i32b_array (v v_NTT_BASE_BOUND +
              6 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
            simd_unit_future.f_values) =
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    simd_unit_ntt_step simd_unit zeta (mk_usize 0) (mk_usize 4)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    simd_unit_ntt_step simd_unit zeta (mk_usize 1) (mk_usize 4)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    simd_unit_ntt_step simd_unit zeta (mk_usize 2) (mk_usize 4)
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    simd_unit_ntt_step simd_unit zeta (mk_usize 3) (mk_usize 4)
  in
  simd_unit

#pop-options

#push-options "--z3rlimit 100"

[@@ "opaque_to_smt"]

let ntt_at_layer_0___round
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (index: usize)
      (zeta_0_ zeta_1_ zeta_2_ zeta_3_: i32)
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (requires
        v index < v Libcrux_ml_dsa.Simd.Traits.v_SIMD_UNITS_IN_RING_ELEMENT /\
        Spec.Utils.is_i32b_array_opaque (v v_NTT_BASE_BOUND +
            7 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
          (Seq.index re (v index)).f_values /\ Spec.Utils.is_i32b 4190208 zeta_0_ /\
        Spec.Utils.is_i32b 4190208 zeta_1_ /\ Spec.Utils.is_i32b 4190208 zeta_2_ /\
        Spec.Utils.is_i32b 4190208 zeta_3_)
      (ensures
        fun re_future ->
          let re_future:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
            (mk_usize 32) =
            re_future
          in
          Spec.Utils.modifies1_32 re re_future index /\
          Spec.Utils.is_i32b_array_opaque (v v_NTT_BASE_BOUND +
              8 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
            (Seq.index re_future (v index)).f_values) =
  let _:Prims.unit =
    reveal_opaque (`%Spec.Utils.is_i32b_array_opaque) (Spec.Utils.is_i32b_array_opaque)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      index
      (simd_unit_ntt_at_layer_0_ (re.[ index ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
          zeta_0_
          zeta_1_
          zeta_2_
          zeta_3_
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
  in
  re

#pop-options

#push-options "--z3rlimit 400 --split_queries always"

let is_i32b_polynomial (b:nat) (re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (sz 32)) =
        Spec.Utils.forall32 (fun x -> Spec.Utils.is_i32b_array_opaque b (Seq.index re x).f_values)

[@@ "opaque_to_smt"]

let ntt_at_layer_0_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (requires
        is_i32b_polynomial (v v_NTT_BASE_BOUND + 7 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
          re)
      (ensures
        fun re_future ->
          let re_future:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
            (mk_usize 32) =
            re_future
          in
          is_i32b_polynomial (v v_NTT_BASE_BOUND +
              8 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
            re_future) =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 0)
      (mk_i32 2091667)
      (mk_i32 3407706)
      (mk_i32 2316500)
      (mk_i32 3817976)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 1)
      (mk_i32 (-3342478))
      (mk_i32 2244091)
      (mk_i32 (-2446433))
      (mk_i32 (-3562462))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 2)
      (mk_i32 266997)
      (mk_i32 2434439)
      (mk_i32 (-1235728))
      (mk_i32 3513181)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 3)
      (mk_i32 (-3520352))
      (mk_i32 (-3759364))
      (mk_i32 (-1197226))
      (mk_i32 (-3193378))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 4)
      (mk_i32 900702)
      (mk_i32 1859098)
      (mk_i32 909542)
      (mk_i32 819034)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 5)
      (mk_i32 495491)
      (mk_i32 (-1613174))
      (mk_i32 (-43260))
      (mk_i32 (-522500))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 6)
      (mk_i32 (-655327))
      (mk_i32 (-3122442))
      (mk_i32 2031748)
      (mk_i32 3207046)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 7)
      (mk_i32 (-3556995))
      (mk_i32 (-525098))
      (mk_i32 (-768622))
      (mk_i32 (-3595838))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 8)
      (mk_i32 342297)
      (mk_i32 286988)
      (mk_i32 (-2437823))
      (mk_i32 4108315)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 9)
      (mk_i32 3437287)
      (mk_i32 (-3342277))
      (mk_i32 1735879)
      (mk_i32 203044)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 10)
      (mk_i32 2842341)
      (mk_i32 2691481)
      (mk_i32 (-2590150))
      (mk_i32 1265009)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 11)
      (mk_i32 4055324)
      (mk_i32 1247620)
      (mk_i32 2486353)
      (mk_i32 1595974)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 12)
      (mk_i32 (-3767016))
      (mk_i32 1250494)
      (mk_i32 2635921)
      (mk_i32 (-3548272))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 13)
      (mk_i32 (-2994039))
      (mk_i32 1869119)
      (mk_i32 1903435)
      (mk_i32 (-1050970))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 14)
      (mk_i32 (-1333058))
      (mk_i32 1237275)
      (mk_i32 (-3318210))
      (mk_i32 (-1430225))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 15)
      (mk_i32 (-451100))
      (mk_i32 1312455)
      (mk_i32 3306115)
      (mk_i32 (-1962642))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 16)
      (mk_i32 (-1279661))
      (mk_i32 1917081)
      (mk_i32 (-2546312))
      (mk_i32 (-1374803))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 17)
      (mk_i32 1500165)
      (mk_i32 777191)
      (mk_i32 2235880)
      (mk_i32 3406031)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 18)
      (mk_i32 (-542412))
      (mk_i32 (-2831860))
      (mk_i32 (-1671176))
      (mk_i32 (-1846953))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 19)
      (mk_i32 (-2584293))
      (mk_i32 (-3724270))
      (mk_i32 594136)
      (mk_i32 (-3776993))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 20)
      (mk_i32 (-2013608))
      (mk_i32 2432395)
      (mk_i32 2454455)
      (mk_i32 (-164721))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 21)
      (mk_i32 1957272)
      (mk_i32 3369112)
      (mk_i32 185531)
      (mk_i32 (-1207385))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 22)
      (mk_i32 (-3183426))
      (mk_i32 162844)
      (mk_i32 1616392)
      (mk_i32 3014001)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 23)
      (mk_i32 810149)
      (mk_i32 1652634)
      (mk_i32 (-3694233))
      (mk_i32 (-1799107))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 24)
      (mk_i32 (-3038916))
      (mk_i32 3523897)
      (mk_i32 3866901)
      (mk_i32 269760)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 25)
      (mk_i32 2213111)
      (mk_i32 (-975884))
      (mk_i32 1717735)
      (mk_i32 472078)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 26)
      (mk_i32 (-426683))
      (mk_i32 1723600)
      (mk_i32 (-1803090))
      (mk_i32 1910376)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 27)
      (mk_i32 (-1667432))
      (mk_i32 (-1104333))
      (mk_i32 (-260646))
      (mk_i32 (-3833893))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 28)
      (mk_i32 (-2939036))
      (mk_i32 (-2235985))
      (mk_i32 (-420899))
      (mk_i32 (-2286327))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 29)
      (mk_i32 183443)
      (mk_i32 (-976891))
      (mk_i32 1612842)
      (mk_i32 (-3545687))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 30)
      (mk_i32 (-554416))
      (mk_i32 3919660)
      (mk_i32 (-48306))
      (mk_i32 (-1362209))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0___round re
      (mk_usize 31)
      (mk_i32 3937738)
      (mk_i32 1400424)
      (mk_i32 (-846154))
      (mk_i32 1976782)
  in
  re

#pop-options

#push-options "--z3rlimit 100"

[@@ "opaque_to_smt"]

let ntt_at_layer_1___round
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (index: usize)
      (zeta_0_ zeta_1_: i32)
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (requires
        v index < v Libcrux_ml_dsa.Simd.Traits.v_SIMD_UNITS_IN_RING_ELEMENT /\
        Spec.Utils.is_i32b_array_opaque (v v_NTT_BASE_BOUND +
            6 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
          (Seq.index re (v index)).f_values /\ Spec.Utils.is_i32b 4190208 zeta_0_ /\
        Spec.Utils.is_i32b 4190208 zeta_1_)
      (ensures
        fun re_future ->
          let re_future:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
            (mk_usize 32) =
            re_future
          in
          Spec.Utils.modifies1_32 re re_future index /\
          Spec.Utils.is_i32b_array_opaque (v v_NTT_BASE_BOUND +
              7 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
            (Seq.index re_future (v index)).f_values) =
  let _:Prims.unit =
    reveal_opaque (`%Spec.Utils.is_i32b_array_opaque) (Spec.Utils.is_i32b_array_opaque)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      index
      (simd_unit_ntt_at_layer_1_ (re.[ index ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
          zeta_0_
          zeta_1_
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
  in
  re

#pop-options

#push-options "--z3rlimit 300 --split_queries always"

[@@ "opaque_to_smt"]

let ntt_at_layer_1_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (requires
        is_i32b_polynomial (v v_NTT_BASE_BOUND + 6 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
          re)
      (ensures
        fun re_future ->
          let re_future:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
            (mk_usize 32) =
            re_future
          in
          is_i32b_polynomial (v v_NTT_BASE_BOUND +
              7 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
            re_future) =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 0) (mk_i32 (-3930395)) (mk_i32 (-1528703))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 1) (mk_i32 (-3677745)) (mk_i32 (-3041255))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 2) (mk_i32 (-1452451)) (mk_i32 3475950)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 3) (mk_i32 2176455) (mk_i32 (-1585221))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 4) (mk_i32 (-1257611)) (mk_i32 1939314)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 5) (mk_i32 (-4083598)) (mk_i32 (-1000202))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 6) (mk_i32 (-3190144)) (mk_i32 (-3157330))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 7) (mk_i32 (-3632928)) (mk_i32 126922)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 8) (mk_i32 3412210) (mk_i32 (-983419))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 9) (mk_i32 2147896) (mk_i32 2715295)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 10) (mk_i32 (-2967645)) (mk_i32 (-3693493))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 11) (mk_i32 (-411027)) (mk_i32 (-2477047))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 12) (mk_i32 (-671102)) (mk_i32 (-1228525))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 13) (mk_i32 (-22981)) (mk_i32 (-1308169))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 14) (mk_i32 (-381987)) (mk_i32 1349076)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 15) (mk_i32 1852771) (mk_i32 (-1430430))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 16) (mk_i32 (-3343383)) (mk_i32 264944)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 17) (mk_i32 508951) (mk_i32 3097992)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 18) (mk_i32 44288) (mk_i32 (-1100098))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 19) (mk_i32 904516) (mk_i32 3958618)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 20) (mk_i32 (-3724342)) (mk_i32 (-8578))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 21) (mk_i32 1653064) (mk_i32 (-3249728))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 22) (mk_i32 2389356) (mk_i32 (-210977))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 23) (mk_i32 759969) (mk_i32 (-1316856))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 24) (mk_i32 189548) (mk_i32 (-3553272))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 25) (mk_i32 3159746) (mk_i32 (-1851402))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 26) (mk_i32 (-2409325)) (mk_i32 (-177440))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 27) (mk_i32 1315589) (mk_i32 1341330)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 28) (mk_i32 1285669) (mk_i32 (-1584928))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 29) (mk_i32 (-812732)) (mk_i32 (-1439742))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 30) (mk_i32 (-3019102)) (mk_i32 (-3881060))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1___round re (mk_usize 31) (mk_i32 (-3628969)) (mk_i32 3839961)
  in
  re

#pop-options

#push-options "--z3rlimit 200"

[@@ "opaque_to_smt"]

let ntt_at_layer_2___round
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (index: usize)
      (zeta: i32)
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (requires
        v index < v Libcrux_ml_dsa.Simd.Traits.v_SIMD_UNITS_IN_RING_ELEMENT /\
        Spec.Utils.is_i32b_array_opaque (v v_NTT_BASE_BOUND +
            5 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
          (Seq.index re (v index)).f_values /\ Spec.Utils.is_i32b 4190208 zeta)
      (ensures
        fun re_future ->
          let re_future:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
            (mk_usize 32) =
            re_future
          in
          Spec.Utils.modifies1_32 re re_future index /\
          Spec.Utils.is_i32b_array_opaque (v v_NTT_BASE_BOUND +
              6 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
            (Seq.index re_future (v index)).f_values) =
  let _:Prims.unit =
    reveal_opaque (`%Spec.Utils.is_i32b_array_opaque) (Spec.Utils.is_i32b_array_opaque)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
      index
      (simd_unit_ntt_at_layer_2_ (re.[ index ]
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
          zeta
        <:
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
  in
  re

#pop-options

#push-options "--z3rlimit 400 --split_queries always"

[@@ "opaque_to_smt"]

let ntt_at_layer_2_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (requires
        is_i32b_polynomial (v v_NTT_BASE_BOUND + 5 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
          re)
      (ensures
        fun re_future ->
          let re_future:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
            (mk_usize 32) =
            re_future
          in
          is_i32b_polynomial (v v_NTT_BASE_BOUND +
              6 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
            re_future) =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 0) (mk_i32 2706023)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 1) (mk_i32 95776)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 2) (mk_i32 3077325)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 3) (mk_i32 3530437)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 4) (mk_i32 (-1661693))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 5) (mk_i32 (-3592148))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 6) (mk_i32 (-2537516))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 7) (mk_i32 3915439)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 8) (mk_i32 (-3861115))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 9) (mk_i32 (-3043716))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 10) (mk_i32 3574422)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 11) (mk_i32 (-2867647))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 12) (mk_i32 3539968)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 13) (mk_i32 (-300467))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 14) (mk_i32 2348700)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 15) (mk_i32 (-539299))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 16) (mk_i32 (-1699267))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 17) (mk_i32 (-1643818))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 18) (mk_i32 3505694)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 19) (mk_i32 (-3821735))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 20) (mk_i32 3507263)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 21) (mk_i32 (-2140649))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 22) (mk_i32 (-1600420))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 23) (mk_i32 3699596)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 24) (mk_i32 811944)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 25) (mk_i32 531354)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 26) (mk_i32 954230)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 27) (mk_i32 3881043)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 28) (mk_i32 3900724)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 29) (mk_i32 (-2556880))
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 30) (mk_i32 2071892)
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2___round re (mk_usize 31) (mk_i32 (-2797779))
  in
  re

#pop-options

let layer_bound_factor (step_by:usize) : n:nat{n <= 4} =
    match step_by with
    | MkInt 1 -> 4
    | MkInt 2 -> 3
    | MkInt 4 -> 2
    | MkInt 8 -> 1
    | MkInt 16 -> 0
    | _ -> 0

#push-options "--z3rlimit 600 --split_queries always"

[@@ "opaque_to_smt"]

let outer_3_plus
      (v_OFFSET v_STEP_BY: usize)
      (v_ZETA: i32)
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (requires
        (v v_STEP_BY > 0) /\
        (v v_OFFSET + v v_STEP_BY < v Libcrux_ml_dsa.Simd.Traits.v_SIMD_UNITS_IN_RING_ELEMENT) /\
        (v v_OFFSET + 2 * v v_STEP_BY <= v Libcrux_ml_dsa.Simd.Traits.v_SIMD_UNITS_IN_RING_ELEMENT) /\
        (Spec.Utils.forall32 (fun i ->
                (i >= v v_OFFSET /\ i < (v v_OFFSET + 2 * v v_STEP_BY)) ==>
                Spec.Utils.is_i32b_array_opaque (v v_NTT_BASE_BOUND +
                    ((layer_bound_factor v_STEP_BY) * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX
                    ))
                  (Seq.index re i).f_values)) /\ Spec.Utils.is_i32b 4190208 v_ZETA)
      (ensures
        fun re_future ->
          let re_future:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
            (mk_usize 32) =
            re_future
          in
          Spec.Utils.modifies_range_32 re
            re_future
            v_OFFSET
            ((v_OFFSET +! v_STEP_BY <: usize) +! v_STEP_BY) /\
          (Spec.Utils.forall32 (fun i ->
                  (i >= v v_OFFSET /\ i < (v v_OFFSET + 2 * v v_STEP_BY)) ==>
                  Spec.Utils.is_i32b_array_opaque (v v_NTT_BASE_BOUND +
                      ((layer_bound_factor v_STEP_BY + 1) *
                        v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX))
                    (Seq.index re_future i).f_values))) =
  let orig_re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    Core.Clone.f_clone #(t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          (mk_usize 32))
      #FStar.Tactics.Typeclasses.solve
      re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    Rust_primitives.Hax.Folds.fold_range v_OFFSET
      (v_OFFSET +! v_STEP_BY <: usize)
      (fun re j ->
          let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
            re
          in
          let j:usize = j in
          (Spec.Utils.modifies_range2_32 orig_re
              re
              v_OFFSET
              j
              (v_OFFSET +! v_STEP_BY)
              (j +! v_STEP_BY)) /\
          (Spec.Utils.forall32 (fun i ->
                  ((i >= v v_OFFSET /\ i < v j) \/
                    (i >= v v_OFFSET + v v_STEP_BY /\ i < v j + v v_STEP_BY)) ==>
                  Spec.Utils.is_i32b_array_opaque (v v_NTT_BASE_BOUND +
                      ((layer_bound_factor v_STEP_BY + 1) *
                        v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX))
                    (Seq.index re i).f_values)))
      re
      (fun re j ->
          let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
            re
          in
          let j:usize = j in
          let tmp:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            re.[ j +! v_STEP_BY <: usize ]
          in
          let tmp:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_by_constant tmp v_ZETA
          in
          let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              (j +! v_STEP_BY <: usize)
              (re.[ j ] <: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
          in
          let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              (j +! v_STEP_BY <: usize)
              (Libcrux_ml_dsa.Simd.Portable.Arithmetic.subtract (re.[ j +! v_STEP_BY <: usize ]
                    <:
                    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
                  tmp
                <:
                Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
          in
          let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
              j
              (Libcrux_ml_dsa.Simd.Portable.Arithmetic.add (re.[ j ]
                    <:
                    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
                  tmp
                <:
                Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
          in
          let _:Prims.unit =
            assert ((v v_NTT_BASE_BOUND +
                  ((layer_bound_factor v_STEP_BY) * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)) +
                (v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX) ==
                (v v_NTT_BASE_BOUND +
                  ((layer_bound_factor v_STEP_BY + 1) *
                    v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)))
          in
          re)
  in
  re

#pop-options

let ntt_at_layer_3___v_STEP: usize = mk_usize 8

let ntt_at_layer_3___v_STEP_BY: usize = mk_usize 1

#push-options "--z3rlimit 400 --split_queries always"

[@@ "opaque_to_smt"]

let ntt_at_layer_3_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (requires
        is_i32b_polynomial (v v_NTT_BASE_BOUND + 4 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
          re)
      (ensures
        fun re_future ->
          let re_future:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
            (mk_usize 32) =
            re_future
          in
          is_i32b_polynomial (v v_NTT_BASE_BOUND +
              5 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
            re_future) =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 0) (mk_usize 1) (mk_i32 2725464) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 2) (mk_usize 1) (mk_i32 1024112) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 4) (mk_usize 1) (mk_i32 (-1079900)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 6) (mk_usize 1) (mk_i32 3585928) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 8) (mk_usize 1) (mk_i32 (-549488)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 10) (mk_usize 1) (mk_i32 (-1119584)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 12) (mk_usize 1) (mk_i32 2619752) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 14) (mk_usize 1) (mk_i32 (-2108549)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 16) (mk_usize 1) (mk_i32 (-2118186)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 18) (mk_usize 1) (mk_i32 (-3859737)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 20) (mk_usize 1) (mk_i32 (-1399561)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 22) (mk_usize 1) (mk_i32 (-3277672)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 24) (mk_usize 1) (mk_i32 1757237) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 26) (mk_usize 1) (mk_i32 (-19422)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 28) (mk_usize 1) (mk_i32 4010497) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 30) (mk_usize 1) (mk_i32 280005) re
  in
  re

#pop-options

let ntt_at_layer_4___v_STEP: usize = mk_usize 16

let ntt_at_layer_4___v_STEP_BY: usize = mk_usize 2

#push-options "--z3rlimit 400 --split_queries always"

[@@ "opaque_to_smt"]

let ntt_at_layer_4_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (requires
        is_i32b_polynomial (v v_NTT_BASE_BOUND + 3 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
          re)
      (ensures
        fun re_future ->
          let re_future:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
            (mk_usize 32) =
            re_future
          in
          is_i32b_polynomial (v v_NTT_BASE_BOUND +
              4 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
            re_future) =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 0) (mk_usize 2) (mk_i32 1826347) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 4) (mk_usize 2) (mk_i32 2353451) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 8) (mk_usize 2) (mk_i32 (-359251)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 12) (mk_usize 2) (mk_i32 (-2091905)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 16) (mk_usize 2) (mk_i32 3119733) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 20) (mk_usize 2) (mk_i32 (-2884855)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 24) (mk_usize 2) (mk_i32 3111497) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 28) (mk_usize 2) (mk_i32 2680103) re
  in
  re

#pop-options

let ntt_at_layer_5___v_STEP: usize = mk_usize 32

let ntt_at_layer_5___v_STEP_BY: usize = mk_usize 4

#push-options "--z3rlimit 400 --split_queries always"

[@@ "opaque_to_smt"]

let ntt_at_layer_5_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (requires
        is_i32b_polynomial (v v_NTT_BASE_BOUND + 2 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
          re)
      (ensures
        fun re_future ->
          let re_future:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
            (mk_usize 32) =
            re_future
          in
          is_i32b_polynomial (v v_NTT_BASE_BOUND +
              3 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
            re_future) =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 0) (mk_usize 4) (mk_i32 237124) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 8) (mk_usize 4) (mk_i32 (-777960)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 16) (mk_usize 4) (mk_i32 (-876248)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 24) (mk_usize 4) (mk_i32 466468) re
  in
  re

#pop-options

let ntt_at_layer_6___v_STEP: usize = mk_usize 64

let ntt_at_layer_6___v_STEP_BY: usize = mk_usize 8

#push-options "--z3rlimit 400 --split_queries always"

[@@ "opaque_to_smt"]

let ntt_at_layer_6_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (requires
        is_i32b_polynomial (v v_NTT_BASE_BOUND + 1 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
          re)
      (ensures
        fun re_future ->
          let re_future:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
            (mk_usize 32) =
            re_future
          in
          is_i32b_polynomial (v v_NTT_BASE_BOUND +
              2 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
            re_future) =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 0) (mk_usize 8) (mk_i32 (-2608894)) re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 16) (mk_usize 8) (mk_i32 (-518909)) re
  in
  re

#pop-options

let ntt_at_layer_7___v_STEP: usize = mk_usize 128

let ntt_at_layer_7___v_STEP_BY: usize = mk_usize 16

#push-options "--z3rlimit 400 --split_queries always"

[@@ "opaque_to_smt"]

let ntt_at_layer_7_
      (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (requires is_i32b_polynomial (v v_NTT_BASE_BOUND) re)
      (ensures
        fun re_future ->
          let re_future:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
            (mk_usize 32) =
            re_future
          in
          is_i32b_polynomial (v v_NTT_BASE_BOUND +
              1 * v Libcrux_ml_dsa.Simd.Traits.Specs.v_FIELD_MAX)
            re_future) =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    outer_3_plus (mk_usize 0) (mk_usize 16) (mk_i32 25847) re
  in
  re

#pop-options

#push-options "--z3rlimit 400 --split_queries always"

[@@ "opaque_to_smt"]

let ntt (re: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
    : Prims.Pure (t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32))
      (requires is_i32b_polynomial (v v_NTT_BASE_BOUND) re)
      (fun _ -> Prims.l_True) =
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_7_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_6_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_5_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_4_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_3_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_2_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_1_ re
  in
  let re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (mk_usize 32) =
    ntt_at_layer_0_ re
  in
  re

#pop-options
