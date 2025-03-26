module Libcrux_ml_dsa.Simd.Portable.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Portable.Vector_type in
  ()

#push-options "--z3rlimit 150"

let add (lhs rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
  let e_lhs0:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Core.Clone.f_clone #Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      #FStar.Tactics.Typeclasses.solve
      lhs
  in
  let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #i32
          (lhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
        <:
        usize)
      (fun lhs i ->
          let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = lhs in
          let i:usize = i in
          (forall (j: usize).
              b2t (j <. i <: bool) ==>
              b2t
              ((lhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ j ] <: i32) =.
                ((e_lhs0.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ j ] <: i32) +!
                  (rhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ j ] <: i32)
                  <:
                  i32)
                <:
                bool)) /\
          (forall (j: usize).
              b2t
              ((j >=. i <: bool) &&
                (j <. Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT <: bool)) ==>
              b2t
              ((lhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ j ] <: i32) =.
                (e_lhs0.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ j ] <: i32)
                <:
                bool)))
      lhs
      (fun lhs i ->
          let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = lhs in
          let i:usize = i in
          let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            {
              lhs with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                i
                ((lhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32) +!
                  (rhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          lhs)
  in
  lhs

#pop-options

#push-options "--z3rlimit 150"

let subtract (lhs rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
  let e_lhs0:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Core.Clone.f_clone #Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      #FStar.Tactics.Typeclasses.solve
      lhs
  in
  let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #i32
          (lhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
        <:
        usize)
      (fun lhs i ->
          let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = lhs in
          let i:usize = i in
          (forall (j: usize).
              b2t (j <. i <: bool) ==>
              b2t
              ((lhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ j ] <: i32) =.
                ((e_lhs0.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ j ] <: i32) -!
                  (rhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ j ] <: i32)
                  <:
                  i32)
                <:
                bool)) /\
          (forall (j: usize).
              b2t
              ((j >=. i <: bool) &&
                (j <. Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT <: bool)) ==>
              b2t
              ((lhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ j ] <: i32) =.
                (e_lhs0.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ j ] <: i32)
                <:
                bool)))
      lhs
      (fun lhs i ->
          let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = lhs in
          let i:usize = i in
          let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            {
              lhs with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                i
                ((lhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32) -!
                  (rhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          lhs)
  in
  lhs

#pop-options

#push-options "--z3rlimit 150 --split_queries always"

let get_n_least_significant_bits (n: u8) (value: u64) =
  let res:u64 = value &. ((mk_u64 1 <<! n <: u64) -! mk_u64 1 <: u64) in
  let _:Prims.unit =
    calc ( == ) {
      v res;
      ( == ) { () }
      v (logand value (((mk_u64 1) <<! n) -! (mk_u64 1)));
      ( == ) { () }
      v (logand value (((mk_int 1) <<! n) -! (mk_int 1)));
      ( == ) { () }
      v (logand value (mk_int ((1 * pow2 (v n)) % pow2 64) -! (mk_int 1)));
      ( == ) { (Math.Lemmas.small_mod (pow2 (v n)) (pow2 64);
        Math.Lemmas.pow2_lt_compat 64 (v n)) }
      v (logand value ((mk_int (pow2 (v n))) -! (mk_int 1)));
      ( == ) { (Math.Lemmas.pow2_lt_compat 64 (v n);
        logand_mask_lemma value (v n)) }
      v value % (pow2 (v n));
    }
  in
  res

#pop-options

#push-options "--z3rlimit 500 --split_queries always"

let montgomery_reduce_element (value: i64) =
  let t:u64 =
    (get_n_least_significant_bits v_MONTGOMERY_SHIFT (cast (value <: i64) <: u64) <: u64) *!
    Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
  in
  let _:Prims.unit = assert (v t == (v value % pow2 32) * 58728449) in
  let k:i32 = cast (get_n_least_significant_bits v_MONTGOMERY_SHIFT t <: u64) <: i32 in
  let _:Prims.unit =
    assert (v k == v t @% pow2 32);
    assert (v (cast (k <: i32) <: i64) == v k);
    assert (v (cast (k <: i32) <: i64) < pow2 31);
    assert (v (cast (k <: i32) <: i64) >= - pow2 31);
    assert (v (cast (Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32) <: i64) == 8380417)
  in
  let k_times_modulus:i64 =
    (cast (k <: i32) <: i64) *! (cast (Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32) <: i64)
  in
  let _:Prims.unit =
    Spec.Utils.lemma_mul_i32b (pow2 31) (8380417) k Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS;
    assert (Spec.Utils.is_i64b (pow2 31 * 8380417) k_times_modulus)
  in
  let c:i32 = cast (k_times_modulus >>! v_MONTGOMERY_SHIFT <: i64) <: i32 in
  let _:Prims.unit =
    assert (v k_times_modulus < pow2 63);
    assert (v k_times_modulus / pow2 32 < pow2 31);
    assert (v c == (v k_times_modulus / pow2 32) @% pow2 32);
    assert (v c == v k_times_modulus / pow2 32);
    assert (Spec.Utils.is_i32b 4190209 c)
  in
  let value_high:i32 = cast (value >>! v_MONTGOMERY_SHIFT <: i64) <: i32 in
  let _:Prims.unit =
    assert (v value < pow2 63);
    assert (v value / pow2 32 < pow2 31);
    assert (v value_high == (v value / pow2 32) @% pow2 32);
    Spec.Utils.lemma_div_at_percent (v value) (pow2 32);
    assert (v value_high == (v value / pow2 32));
    assert (Spec.Utils.is_i64b (8380416 * 8380416) value ==> Spec.Utils.is_i32b 8265825 value_high);
    assert (Spec.Utils.is_i32b 8380416 value_high)
  in
  let res:i32 = value_high -! c in
  let _:Prims.unit =
    assert (Spec.Utils.is_i32b (8380416 + 4190209) res);
    assert (Spec.Utils.is_i64b (8380416 * pow2 31) value ==> Spec.Utils.is_i32b 58728448 res)
  in
  let _:Prims.unit =
    calc ( == ) {
      v k_times_modulus % pow2 32;
      ( == ) { assert (v k_times_modulus == v k * 8380417) }
      (v k * 8380417) % pow2 32;
      ( == ) { assert (v k = ((v value % pow2 32) * 58728449) @% pow2 32) }
      ((((v value % pow2 32) * 58728449) @% pow2 32) * 8380417) % pow2 32;
      ( == ) { Math.Lemmas.lemma_mod_sub ((((v value % pow2 32) * 58728449) % pow2 32) * 8380417)
        (pow2 32)
        8380417 }
      ((((v value % pow2 32) * 58728449) % pow2 32) * 8380417) % pow2 32;
      ( == ) { Math.Lemmas.lemma_mod_mul_distr_l ((v value % pow2 32) * 58728449) 8380417 (pow2 32) }
      ((((v value % pow2 32) * 58728449) * 8380417) % pow2 32);
      ( == ) { Math.Lemmas.lemma_mod_mul_distr_r (v value % pow2 32) (58728449 * 8380417) (pow2 32) }
      ((v value % pow2 32) % pow2 32);
      ( == ) { Math.Lemmas.lemma_mod_sub (v value) (pow2 32) 1 }
      (v value) % pow2 32;
    };
    Math.Lemmas.modulo_add (pow2 32) (- (v k_times_modulus)) (v value) (v k_times_modulus);
    assert ((v value - v k_times_modulus) % pow2 32 == 0)
  in
  let _:Prims.unit =
    calc ( == ) {
      v res % 8380417;
      ( == ) { assert (v res == v value_high - v c) }
      (v value / pow2 32 - v k_times_modulus / pow2 32) % 8380417;
      ( == ) { Math.Lemmas.lemma_div_exact (v value - v k_times_modulus) (pow2 32) }
      ((v value - v k_times_modulus) / pow2 32) % 8380417;
      ( == ) { assert ((pow2 32 * 8265825) % 8380417 == 1) }
      (((v value - v k_times_modulus) / pow2 32) * ((pow2 32 * 8265825) % 8380417)) % 8380417;
      ( == ) { Math.Lemmas.lemma_mod_mul_distr_r ((v value - v k_times_modulus) / pow2 32)
        (pow2 32 * 8265825)
        8380417 }
      (((v value - v k_times_modulus) / pow2 32) * pow2 32 * 8265825) % 8380417;
      ( == ) { Math.Lemmas.lemma_div_exact (v value - v k_times_modulus) (pow2 32) }
      ((v value - v k_times_modulus) * 8265825) % 8380417;
      ( == ) { assert (v k_times_modulus == (v k @% pow2 32) * 8380417) }
      ((v value * 8265825) - ((v k @% pow2 32) * 8380417 * 8265825)) % 8380417;
      ( == ) { Math.Lemmas.lemma_mod_sub (v value * 8265825) 8380417 ((v k @% pow2 32) * 8265825) }
      (v value * 8265825) % 8380417;
    }
  in
  res

#pop-options

#push-options "--z3rlimit 300"

let montgomery_multiply_fe_by_fer (fe fer: i32) =
  let _:Prims.unit = Spec.Utils.lemma_mul_i32b (pow2 31) (4190208) fe fer in
  montgomery_reduce_element ((cast (fe <: i32) <: i64) *! (cast (fer <: i32) <: i64) <: i64)

#pop-options

#push-options "--z3rlimit 150"

let montgomery_multiply_by_constant
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (c: i32)
     =
  let e_simd_unit0:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Core.Clone.f_clone #Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      #FStar.Tactics.Typeclasses.solve
      simd_unit
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #i32
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
        <:
        usize)
      (fun simd_unit i ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = simd_unit in
          let i:usize = i in
          (forall j.
              j < v i ==>
              (let vecj = Seq.index simd_unit.f_values j in
                (Spec.Utils.is_i32b 8380416 vecj /\
                  v vecj % 8380417 ==
                  (v (Seq.index e_simd_unit0.f_values j) * v c * 8265825) % 8380417))) /\
          (forall j.
              j >= v i ==> (Seq.index simd_unit.f_values j) == (Seq.index e_simd_unit0.f_values j)))
      simd_unit
      (fun simd_unit i ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = simd_unit in
          let i:usize = i in
          let _:Prims.unit =
            Spec.Utils.lemma_mul_i32b (pow2 31) (4190208) simd_unit.f_values.[ i ] c
          in
          {
            simd_unit with
            Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              i
              (montgomery_reduce_element ((cast (simd_unit
                            .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ]
                          <:
                          i32)
                      <:
                      i64) *!
                    (cast (c <: i32) <: i64)
                    <:
                    i64)
                <:
                i32)
          }
          <:
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
  in
  simd_unit

#pop-options

#push-options "--z3rlimit 150"

let montgomery_multiply (lhs rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
  let e_lhs0:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Core.Clone.f_clone #Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      #FStar.Tactics.Typeclasses.solve
      lhs
  in
  let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #i32
          (lhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
        <:
        usize)
      (fun lhs i ->
          let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = lhs in
          let i:usize = i in
          (forall j.
              j < v i ==>
              (let vecj = Seq.index lhs.f_values j in
                (Spec.Utils.is_i32b 8380416 vecj /\
                  v vecj % 8380417 ==
                  (v (Seq.index e_lhs0.f_values j) * v (Seq.index rhs.f_values j) * 8265825) %
                  8380417))) /\
          (forall j. j >= v i ==> (Seq.index lhs.f_values j) == (Seq.index e_lhs0.f_values j)))
      lhs
      (fun lhs i ->
          let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = lhs in
          let i:usize = i in
          let _:Prims.unit =
            Spec.Utils.lemma_mul_i32b (pow2 31) (4190208) lhs.f_values.[ i ] rhs.f_values.[ i ]
          in
          {
            lhs with
            Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs
                .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              i
              (montgomery_reduce_element ((cast (lhs
                            .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ]
                          <:
                          i32)
                      <:
                      i64) *!
                    (cast (rhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32)
                      <:
                      i64)
                    <:
                    i64)
                <:
                i32)
          }
          <:
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
  in
  lhs

#pop-options

#push-options "--ext context_pruning --z3refresh --split_queries always"

let power2round_element (t: i32) =
  let _:Prims.unit = logand_lemma Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS (t >>! mk_i32 31) in
  let e_t:i32 = t in
  let t:i32 =
    t +! ((t >>! mk_i32 31 <: i32) &. Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32)
  in
  let _:Prims.unit = assert (v t == v e_t % v Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS) in
  let t1:i32 =
    ((t -! mk_i32 1 <: i32) +!
      (mk_i32 1 <<! (Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T -! mk_usize 1 <: usize)
        <:
        i32)
      <:
      i32) >>!
    Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T
  in
  let _:Prims.unit =
    assert (v t1 == (v t - 1 + pow2 12) / pow2 13);
    assert ((v t - (Spec.Utils.mod_p (v t) (pow2 13))) / pow2 13 ==
        (v t / pow2 13 - (Spec.Utils.mod_p (v t) (pow2 13)) / pow2 13));
    if v t % pow2 13 > pow2 12
    then
      (assert (Spec.Utils.mod_p (v t) (pow2 13) == v t % pow2 13 - pow2 13);
        assert ((Spec.Utils.mod_p (v t) (pow2 13)) / pow2 13 == (v t % pow2 13 - pow2 13) / pow2 13);
        assert ((v t % pow2 13 - pow2 13) / pow2 13 == (v t % pow2 13) / pow2 13 - pow2 13 / pow2 13
          );
        assert ((v t % pow2 13) / pow2 13 - pow2 13 / pow2 13 == - 1);
        assert ((v t - (Spec.Utils.mod_p (v t) (pow2 13))) / pow2 13 == v t / pow2 13 + 1))
    else
      (assert ((v t - (Spec.Utils.mod_p (v t) (pow2 13))) / pow2 13 == v t / pow2 13);
        assert ((v t - 1 + pow2 12) / pow2 13 == v t / pow2 13));
    assert (v t1 == (v t - (Spec.Utils.mod_p (v t) (pow2 13))) / pow2 13)
  in
  let t0:i32 = t -! (t1 <<! Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T <: i32) in
  let _:Prims.unit =
    assert (v t0 == v t - ((v t - (Spec.Utils.mod_p (v t) (pow2 13))) / pow2 13) * pow2 13);
    assert (v t0 == v t - (v t - (Spec.Utils.mod_p (v t) (pow2 13))));
    assert (v t0 == Spec.Utils.mod_p (v t) (pow2 13))
  in
  t0, t1 <: (i32 & i32)

#pop-options

let power2round (t0 t1: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
  let (e_t0: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients):Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
  =
    Core.Clone.f_clone #Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      #FStar.Tactics.Typeclasses.solve
      t0
  in
  let t0, t1:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #i32
          (t0.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
        <:
        usize)
      (fun temp_0_ i ->
          let t0, t1:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
            temp_0_
          in
          let i:usize = i in
          (forall j.
              j < v i ==>
              (let t0_v = v (Seq.index t0.f_values j) in
                let t0_s, t1_s = Spec.MLDSA.Math.power2round (v (Seq.index e_t0.f_values j)) in
                t0_v == t0_s /\ v (Seq.index t1.f_values j) == t1_s /\
                Spec.Utils.is_intb_bt (pow2 (v Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T -
                        1))
                  t0_v)) /\
          (forall j.
              j >= v i ==>
              (Seq.index t0.f_values j == Seq.index e_t0.f_values j /\
                Spec.Utils.is_i32b (v Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS - 1)
                  (Seq.index t0.f_values j))))
      (t0, t1
        <:
        (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients))
      (fun temp_0_ i ->
          let t0, t1:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
            temp_0_
          in
          let i:usize = i in
          let lhs, lhs_1_:(i32 & i32) =
            power2round_element (t0.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32)
          in
          let t0:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            {
              t0 with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize t0
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                i
                lhs
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          let t1:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            {
              t1 with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize t1
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                i
                lhs_1_
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          let _:Prims.unit = () in
          t0, t1
          <:
          (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients))
  in
  t0, t1
  <:
  (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)

let infinity_norm_exceeds
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (bound: i32)
     =
  let result:bool = false in
  let result:bool =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #i32
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
        <:
        usize)
      (fun result i ->
          let result:bool = result in
          let i:usize = i in
          result == false ==>
          (forall j. j < v i ==> abs (v (Seq.index simd_unit.f_values j)) < v bound))
      result
      (fun result i ->
          let result:bool = result in
          let i:usize = i in
          let coefficient:i32 = simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] in
          let sign:i32 = coefficient >>! mk_i32 31 in
          let _:Prims.unit = logand_lemma (mk_i32 2 *! coefficient) sign in
          let normalized:i32 = coefficient -! (sign &. (mk_i32 2 *! coefficient <: i32) <: i32) in
          let _:Prims.unit = assert (v normalized == abs (v coefficient)) in
          let result:bool = result || normalized >=. bound in
          result)
  in
  result

let reduce_element (fe: i32) =
  let quotient:i32 = (fe +! (mk_i32 1 <<! mk_i32 22 <: i32) <: i32) >>! mk_i32 23 in
  let result:i32 = fe -! (quotient *! Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32) in
  let _:Prims.unit =
    calc ( == ) {
      v result % 8380417;
      ( == ) { () }
      (v fe - (v quotient * 8380417)) % 8380417;
      ( == ) { Math.Lemmas.lemma_mod_sub_distr (v fe) (v quotient * 8380417) 8380417 }
      (v fe - (v quotient * 8380417) % 8380417) % 8380417;
      ( == ) { Math.Lemmas.cancel_mul_mod (v quotient) 8380417 }
      (v fe - 0) % 8380417;
      ( == ) { () }
      (v fe) % 8380417;
    }
  in
  result

let shift_left_then_reduce
      (v_SHIFT_BY: i32)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
     =
  let e_simd_unit0:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Core.Clone.f_clone #Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      #FStar.Tactics.Typeclasses.solve
      simd_unit
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #i32
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
        <:
        usize)
      (fun simd_unit i ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = simd_unit in
          let i:usize = i in
          (forall j.
              j < v i ==>
              (Spec.Utils.is_i32b 8380416 (Seq.index simd_unit.f_values j) /\
                v (Seq.index simd_unit.f_values j) % 8380417 ==
                (v ((Seq.index e_simd_unit0.f_values j) <<! v_SHIFT_BY) % 8380417))) /\
          (forall j.
              j >= v i ==>
              (Seq.index simd_unit.f_values j == Seq.index e_simd_unit0.f_values j /\
                Spec.Utils.is_i32b 2143289343 ((Seq.index simd_unit.f_values j) <<! v_SHIFT_BY))))
      simd_unit
      (fun simd_unit i ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = simd_unit in
          let i:usize = i in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                i
                (reduce_element ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ]
                        <:
                        i32) <<!
                      v_SHIFT_BY
                      <:
                      i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          simd_unit)
  in
  simd_unit

let compute_one_hint (low high gamma2: i32) =
  if
    low >. gamma2 || low <. (Core.Ops.Arith.f_neg gamma2 <: i32) ||
    low =. (Core.Ops.Arith.f_neg gamma2 <: i32) && high <>. mk_i32 0
  then mk_i32 1
  else mk_i32 0

let compute_hint
      (low high: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (gamma2: i32)
      (hint: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
     =
  let one_hints_count:usize = mk_usize 0 in
  let _:Prims.unit =
    Lib.LoopCombinators.eq_repeati0 0 (Spec.MLDSA.Math.hint_counter hint.f_values) 0
  in
  let hint, one_hints_count:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #i32
          (hint.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
        <:
        usize)
      (fun temp_0_ i ->
          let hint, one_hints_count:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & usize
          ) =
            temp_0_
          in
          let i:usize = i in
          v i >= 0 /\ v i <= 8 /\
          (forall j.
              j < v i ==>
              (v (Seq.index hint.f_values j) =
                Spec.MLDSA.Math.compute_one_hint (v (Seq.index low.f_values j))
                  (v (Seq.index high.f_values j))
                  (v gamma2))) /\ v one_hints_count <= v i /\
          v one_hints_count ==
          Lib.LoopCombinators.repeati (v i) (Spec.MLDSA.Math.hint_counter hint.f_values) 0)
      (hint, one_hints_count <: (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & usize))
      (fun temp_0_ i ->
          let hint, one_hints_count:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & usize
          ) =
            temp_0_
          in
          let i:usize = i in
          let e_hint_values:t_Array i32 (mk_usize 8) =
            hint.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
          in
          let hint:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            {
              hint with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hint
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                i
                (compute_one_hint (low.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ]
                      <:
                      i32)
                    (high.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32)
                    gamma2
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          let _:Prims.unit =
            Spec.MLDSA.Math.hint_counter_loop hint.f_values e_hint_values (v i);
            Lib.LoopCombinators.unfold_repeati (v i + 1)
              (Spec.MLDSA.Math.hint_counter hint.f_values)
              0
              (v i)
          in
          let one_hints_count:usize =
            one_hints_count +!
            (cast (hint.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32) <: usize)
          in
          hint, one_hints_count <: (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & usize)
      )
  in
  let hax_temp_output:usize = one_hints_count in
  hint, hax_temp_output <: (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & usize)

#push-options "--fuel 3 --z3rlimit 1500 --ext context_pruning --z3refresh --split_queries always"

let decompose_element (gamma2 r: i32) =
  let e_r:i32 = r in
  let _:Prims.unit = logand_lemma Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS (r >>! mk_i32 31) in
  let r:i32 =
    r +! ((r >>! mk_i32 31 <: i32) &. Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32)
  in
  let _:Prims.unit = assert (v r == v e_r % v Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS) in
  let ceil_of_r_by_128_:i32 = (r +! mk_i32 127 <: i32) >>! mk_i32 7 in
  let _:Prims.unit = assert (v ceil_of_r_by_128_ == (v r + 127) / 128) in
  let r1:i32 =
    match gamma2 <: i32 with
    | Rust_primitives.Integers.MkInt 95232 ->
      let result:i32 =
        ((ceil_of_r_by_128_ *! mk_i32 11275 <: i32) +! (mk_i32 1 <<! mk_i32 23 <: i32) <: i32) >>!
        mk_i32 24
      in
      let _:Prims.unit =
        assert (v result == ((v ceil_of_r_by_128_ * 11275) + pow2 23) / pow2 24);
        assert (v result == ((((v r + 127) / 128) * 11275) + pow2 23) / pow2 24);
        assert (v result == (v r - 1 + 95232) / 190464);
        assert (v result == (v r - (Spec.Utils.mod_p (v r) 190464)) / 190464);
        assert (v result >= 0 /\ v result <= 44)
      in
      let _:Prims.unit =
        logxor_lemma result ((mk_i32 43 -! result) >>! mk_i32 31);
        lognot_lemma result;
        logand_lemma (result ^. ((mk_i32 43 -! result) >>! mk_i32 31)) result
      in
      let result_0_:i32 =
        (result ^. ((mk_i32 43 -! result <: i32) >>! mk_i32 31 <: i32) <: i32) &. result
      in
      let _:Prims.unit =
        assert (v result == 44 ==> v result_0_ == 0);
        assert (v result < 44 ==> v result_0_ == v result)
      in
      result_0_
    | Rust_primitives.Integers.MkInt 261888 ->
      let result:i32 =
        ((ceil_of_r_by_128_ *! mk_i32 1025 <: i32) +! (mk_i32 1 <<! mk_i32 21 <: i32) <: i32) >>!
        mk_i32 22
      in
      let _:Prims.unit =
        assert (v result == ((v ceil_of_r_by_128_ * 1025) + pow2 21) / pow2 22);
        assert (v result == ((((v r + 127) / 128) * 1025) + pow2 21) / pow2 22);
        assert (v result == (v r - 1 + 261888) / 523776);
        assert (v result == (v r - (Spec.Utils.mod_p (v r) 523776)) / 523776);
        assert (v result >= 0 /\ v result <= 16)
      in
      let _:Prims.unit = logand_mask_lemma result 4 in
      let result_0_:i32 = result &. mk_i32 15 in
      let _:Prims.unit =
        assert (v result == 16 ==> v result_0_ == 0);
        assert (v result < 16 ==> v result_0_ == v result)
      in
      result_0_
    | _ ->
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

          <:
          Rust_primitives.Hax.t_Never)
  in
  let alpha:i32 = gamma2 *! mk_i32 2 in
  let r0:i32 = r -! (r1 *! alpha <: i32) in
  let e_r0:i32 = r0 in
  let _:Prims.unit =
    logand_lemma ((((Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS -! mk_i32 1) /! mk_i32 2) -! r0) >>!
        mk_i32 31)
      Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
  in
  let r0:i32 =
    r0 -!
    (((((Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS -! mk_i32 1 <: i32) /! mk_i32 2 <: i32) -! r0
          <:
          i32) >>!
        mk_i32 31
        <:
        i32) &.
      Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
      <:
      i32)
  in
  let _:Prims.unit =
    assert (v e_r0 > 4190208 ==> v r0 == v e_r0 - 8380417);
    assert (v e_r0 <= 4190208 ==> v r0 == v e_r0);
    if v r - (Spec.Utils.mod_p (v r) (v alpha)) = 8380416
    then
      (assert (v r1 == 0);
        assert (v r0 == (Spec.Utils.mod_p (v r) (v alpha)) - 1);
        assert (v r0 >= - (v gamma2) /\ v r0 < 0))
    else
      (assert (v r1 == (v r - (Spec.Utils.mod_p (v r) (v alpha))) / v alpha);
        assert (v r0 == Spec.Utils.mod_p (v r) (v alpha));
        assert (v r0 > - (v gamma2) /\ v r0 <= v gamma2));
    assert (v r1 >= 0 /\ v r1 < 8380416 / (v alpha))
  in
  r0, r1 <: (i32 & i32)

#pop-options

#push-options "--ext context_pruning --z3refresh --split_queries always"

let uuse_one_hint (gamma2 r hint: i32) =
  let r0, r1:(i32 & i32) = decompose_element gamma2 r in
  if hint =. mk_i32 0
  then r1
  else
    match gamma2 <: i32 with
    | Rust_primitives.Integers.MkInt 95232 ->
      if r0 >. mk_i32 0
      then if r1 =. mk_i32 43 then mk_i32 0 else r1 +! hint
      else if r1 =. mk_i32 0 then mk_i32 43 else r1 -! hint
    | Rust_primitives.Integers.MkInt 261888 ->
      let _:Prims.unit =
        logand_mask_lemma (r1 +! hint) 4;
        logand_mask_lemma (r1 -! hint) 4
      in
      if r0 >. mk_i32 0 then (r1 +! hint <: i32) &. mk_i32 15 else (r1 -! hint <: i32) &. mk_i32 15
    | _ ->
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

          <:
          Rust_primitives.Hax.t_Never)

#pop-options

let decompose
      (gamma2: i32)
      (simd_unit low high: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
     =
  let high, low:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #i32
          (low.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
        <:
        usize)
      (fun temp_0_ i ->
          let high, low:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
            temp_0_
          in
          let i:usize = i in
          forall j.
            j < v i ==>
            (let r = v (Seq.index simd_unit.f_values j) in
              let r0 = v (Seq.index low.f_values j) in
              let r1 = v (Seq.index high.f_values j) in
              let r0_s, r1_s, cond = Spec.MLDSA.Math.decompose (v gamma2) r in
              r0 = r0_s /\ r1 = r1_s /\
              (if cond
                then (r0 >= - (v gamma2) /\ r0 < 0)
                else (r0 > - (v gamma2) /\ r0 <= v gamma2)) /\
              (r1 >= 0 /\ r1 < (v Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS - 1) / (v gamma2 * 2)))
      )
      (high, low
        <:
        (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients))
      (fun temp_0_ i ->
          let high, low:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
            temp_0_
          in
          let i:usize = i in
          let lhs, lhs_1_:(i32 & i32) =
            decompose_element gamma2
              (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32)
          in
          let low:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            {
              low with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                i
                lhs
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          let high:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            {
              high with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                i
                lhs_1_
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          let _:Prims.unit = () in
          high, low
          <:
          (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients))
  in
  low, high
  <:
  (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)

let uuse_hint
      (gamma2: i32)
      (simd_unit hint: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
     =
  let e_hint0:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Core.Clone.f_clone #Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      #FStar.Tactics.Typeclasses.solve
      hint
  in
  let hint:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #i32
          (hint.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
        <:
        usize)
      (fun hint i ->
          let hint:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = hint in
          let i:usize = i in
          (forall j.
              j < v i ==>
              (let h = Seq.index e_hint0.f_values j in
                let result = Seq.index hint.f_values j in
                v result =
                Spec.MLDSA.Math.use_one_hint (v gamma2) (v (Seq.index simd_unit.f_values j)) (v h))) /\
          (forall j.
              j >= v i ==>
              (Seq.index hint.f_values j == Seq.index e_hint0.f_values j /\
                (v (Seq.index hint.f_values j) == 0 \/ v (Seq.index hint.f_values j) == 1))))
      hint
      (fun hint i ->
          let hint:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = hint in
          let i:usize = i in
          let hint:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            {
              hint with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hint
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                i
                (uuse_one_hint gamma2
                    (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32)
                    (hint.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          hint)
  in
  hint
