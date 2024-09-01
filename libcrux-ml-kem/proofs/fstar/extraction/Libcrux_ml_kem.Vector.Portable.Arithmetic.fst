module Libcrux_ml_kem.Vector.Portable.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

#push-options "--z3rlimit 150 --split_queries always"

let get_n_least_significant_bits (n: u8) (value: u32) =
  let res:u32 = value &. ((1ul <<! n <: u32) -! 1ul <: u32) in
  let _:Prims.unit =
    calc ( == ) {
      v res;
      ( == ) { () }
      v (logand value ((1ul <<! n) -! 1ul));
      ( == ) { mk_int_equiv_lemma #u32_inttype 1 }
      v (logand value (((mk_int 1) <<! n) -! (mk_int 1)));
      ( == ) { () }
      v (logand value (mk_int ((1 * pow2 (v n)) % pow2 32) -! (mk_int 1)));
      ( == ) { (Math.Lemmas.small_mod (pow2 (v n)) (pow2 32);
        Math.Lemmas.pow2_lt_compat 32 (v n)) }
      v (logand value ((mk_int (pow2 (v n))) -! (mk_int 1)));
      ( == ) { (Math.Lemmas.pow2_lt_compat 32 (v n);
        logand_mask_lemma value (v n)) }
      v value % (pow2 (v n));
    }
  in
  res

#pop-options

#push-options "--z3rlimit 150"

let barrett_reduce_element (value: i16) =
  let t:i32 =
    ((Core.Convert.f_from #i32 #i16 #FStar.Tactics.Typeclasses.solve value <: i32) *!
      v_BARRETT_MULTIPLIER
      <:
      i32) +!
    (Libcrux_ml_kem.Vector.Traits.v_BARRETT_R >>! 1l <: i32)
  in
  let _:Prims.unit =
    assert_norm (v v_BARRETT_MULTIPLIER == (pow2 27 + 3329) / (2 * 3329));
    assert (v t = v value * v v_BARRETT_MULTIPLIER + pow2 25)
  in
  let _:Prims.unit = assert (v t / pow2 26 < 9) in
  let _:Prims.unit = assert (v t / pow2 26 > - 9) in
  let quotient:i16 = cast (t >>! Libcrux_ml_kem.Vector.Traits.v_BARRETT_SHIFT <: i32) <: i16 in
  let _:Prims.unit = assert (v quotient = v t / pow2 26) in
  let _:Prims.unit = assert (Spec.Utils.is_i16b 9 quotient) in
  let result:i16 = value -! (quotient *! Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) in
  let _:Prims.unit =
    calc ( == ) {
      v result % 3329;
      ( == ) { () }
      (v value - (v quotient * 3329)) % 3329;
      ( == ) { Math.Lemmas.lemma_mod_sub_distr (v value) (v quotient * 3329) 3329 }
      (v value - (v quotient * 3329) % 3329) % 3329;
      ( == ) { Math.Lemmas.cancel_mul_mod (v quotient) 3329 }
      (v value - 0) % 3329;
      ( == ) { () }
      (v value) % 3329;
    }
  in
  result

#pop-options

#push-options "--z3rlimit 500 --split_queries always"

let montgomery_reduce_element (value: i32) =
  let _:i32 = v_MONTGOMERY_R in
  let k:i32 =
    (cast (cast (value <: i32) <: i16) <: i32) *!
    (cast (Libcrux_ml_kem.Vector.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R <: u32) <: i32)
  in
  let _:Prims.unit =
    assert (v (cast (cast (value <: i32) <: i16) <: i32) == v value @% pow2 16);
    assert (v k == (v value @% pow2 16) * 62209);
    assert (v (cast (cast (k <: i32) <: i16) <: i32) == v k @% pow2 16);
    assert (v (cast (cast (k <: i32) <: i16) <: i32) < pow2 15);
    assert (v (cast (cast (k <: i32) <: i16) <: i32) >= - pow2 15);
    assert (v (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) <: i32) == 3329)
  in
  let k_times_modulus:i32 =
    (cast (cast (k <: i32) <: i16) <: i32) *!
    (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) <: i32)
  in
  let _:Prims.unit =
    Spec.Utils.lemma_mul_i16b (pow2 15)
      (3329)
      (cast (k <: i32) <: i16)
      Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS;
    assert (Spec.Utils.is_i32b (pow2 15 * 3329) k_times_modulus)
  in
  let c:i16 = cast (k_times_modulus >>! v_MONTGOMERY_SHIFT <: i32) <: i16 in
  let _:Prims.unit =
    assert (v k_times_modulus < pow2 31);
    assert (v k_times_modulus / pow2 16 < pow2 15);
    assert (v c == (v k_times_modulus / pow2 16) @% pow2 16);
    assert (v c == v k_times_modulus / pow2 16);
    assert (Spec.Utils.is_i16b 1665 c)
  in
  let value_high:i16 = cast (value >>! v_MONTGOMERY_SHIFT <: i32) <: i16 in
  let _:Prims.unit =
    assert (v value < pow2 31);
    assert (v value / pow2 16 < pow2 15);
    assert (v value_high == (v value / pow2 16) @% pow2 16);
    assert ((v value / pow2 16) < pow2 15 ==> (v value / pow2 16) @% pow2 16 == (v value / pow2 16));
    assert (v value_high == (v value / pow2 16));
    assert (Spec.Utils.is_i32b (3328 * 3328) value ==> Spec.Utils.is_i16b 169 value_high);
    assert (Spec.Utils.is_i16b 3328 value_high)
  in
  let res:i16 = value_high -! c in
  let _:Prims.unit = assert (Spec.Utils.is_i16b (3328 + 1665) res) in
  let _:Prims.unit =
    assert (Spec.Utils.is_i32b (3328 * 3328) value ==> Spec.Utils.is_i16b 3328 res)
  in
  let _:Prims.unit =
    calc ( == ) {
      v k_times_modulus % pow2 16;
      ( == ) { assert (v k_times_modulus == (v k @% pow2 16) * 3329) }
      ((v k @% pow2 16) * 3329) % pow2 16;
      ( == ) { assert (v k = (v value @% pow2 16) * 62209) }
      ((((v value @% pow2 16) * 62209) @% pow2 16) * 3329) % pow2 16;
      ( == ) { Math.Lemmas.lemma_mod_sub ((((v value @% pow2 16) * 62209) % pow2 16) * 3329)
        (pow2 16)
        3329 }
      ((((v value @% pow2 16) * 62209) % pow2 16) * 3329) % pow2 16;
      ( == ) { Math.Lemmas.lemma_mod_mul_distr_l ((v value @% pow2 16) * 62209) 3329 (pow2 16) }
      ((((v value @% pow2 16) * 62209) * 3329) % pow2 16);
      ( == ) { Math.Lemmas.lemma_mod_mul_distr_r (v value @% pow2 16) (62209 * 3329) (pow2 16) }
      ((v value @% pow2 16) % pow2 16);
      ( == ) { Math.Lemmas.lemma_mod_sub (v value) (pow2 16) 1 }
      (v value) % pow2 16;
    };
    Math.Lemmas.modulo_add (pow2 16) (- (v k_times_modulus)) (v value) (v k_times_modulus);
    assert ((v value - v k_times_modulus) % pow2 16 == 0)
  in
  let _:Prims.unit =
    calc ( == ) {
      v res % 3329;
      ( == ) { assert (v res == v value_high - v c) }
      (v value / pow2 16 - v k_times_modulus / pow2 16) % 3329;
      ( == ) { Math.Lemmas.lemma_div_exact (v value - v k_times_modulus) (pow2 16) }
      ((v value - v k_times_modulus) / pow2 16) % 3329;
      ( == ) { assert ((pow2 16 * 169) % 3329 == 1) }
      (((v value - v k_times_modulus) / pow2 16) * ((pow2 16 * 169) % 3329)) % 3329;
      ( == ) { Math.Lemmas.lemma_mod_mul_distr_r ((v value - v k_times_modulus) / pow2 16)
        (pow2 16 * 169)
        3329 }
      (((v value - v k_times_modulus) / pow2 16) * pow2 16 * 169) % 3329;
      ( == ) { Math.Lemmas.lemma_div_exact (v value - v k_times_modulus) (pow2 16) }
      ((v value - v k_times_modulus) * 169) % 3329;
      ( == ) { assert (v k_times_modulus == (v k @% pow2 16) * 3329) }
      ((v value * 169) - ((v k @% pow2 16) * 3329 * 169)) % 3329;
      ( == ) { Math.Lemmas.lemma_mod_sub (v value * 169) 3329 ((v k @% pow2 16) * 169) }
      (v value * 169) % 3329;
    }
  in
  res

#pop-options

#push-options "--z3rlimit 300"

let montgomery_multiply_fe_by_fer (fe fer: i16) =
  let _:Prims.unit = Spec.Utils.lemma_mul_i16b (pow2 16) (3328) fe fer in
  let product:i32 = (cast (fe <: i16) <: i32) *! (cast (fer <: i16) <: i32) in
  montgomery_reduce_element product

#pop-options

#push-options "--z3rlimit 150"

let add (lhs rhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let v__lhs0:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = lhs in
  let lhs:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun lhs i ->
          let lhs:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = lhs in
          let i:usize = i in
          (forall j.
              j < v i ==>
              (Seq.index lhs.f_elements j) ==
              (Seq.index v__lhs0.f_elements j) +. (Seq.index rhs.f_elements j)) /\
          (forall j. j >= v i ==> (Seq.index lhs.f_elements j) == (Seq.index v__lhs0.f_elements j)))
      lhs
      (fun lhs i ->
          let lhs:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = lhs in
          let i:usize = i in
          let lhs:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
            {
              lhs with
              Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
                i
                (Core.Num.impl__i16__wrapping_add (lhs
                        .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ]
                      <:
                      i16)
                    (rhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16)
                  <:
                  i16)
            }
            <:
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
          in
          lhs)
  in
  let _:Prims.unit =
    Spec.Utils.lemma_map2_index #_ #_ #_ #(sz 16) ( +. ) v__lhs0.f_elements rhs.f_elements;
    Seq.lemma_eq_intro lhs.f_elements (Spec.Utils.map2 ( +. ) v__lhs0.f_elements rhs.f_elements)
  in
  lhs

#pop-options

#push-options "--z3rlimit 150"

let barrett_reduce (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let v__vec0:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun vec i ->
          let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let i:usize = i in
          (forall j.
              j < v i ==>
              (Spec.Utils.is_i16b 3328 (Seq.index vec.f_elements j) /\
                v (Seq.index vec.f_elements j) % 3329 == (v (Seq.index v__vec0.f_elements j) % 3329)
              )) /\
          (forall j.
              j >= v i ==>
              (Seq.index vec.f_elements j == Seq.index v__vec0.f_elements j /\
                Spec.Utils.is_i16b 28296 (Seq.index vec.f_elements j))))
      vec
      (fun vec i ->
          let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let i:usize = i in
          let vi:i16 =
            barrett_reduce_element (vec.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ]
                <:
                i16)
          in
          let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
            {
              vec with
              Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vec
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
                i
                vi
            }
            <:
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
          in
          let _:Prims.unit =
            assert (v (mk_int #usize_inttype (v i + 1)) == v i + 1);
            assert (forall j. j < v i ==> Spec.Utils.is_i16b 3328 (Seq.index vec.f_elements j));
            assert (Spec.Utils.is_i16b 3328 vi);
            assert (Spec.Utils.is_i16b 3328 (Seq.index vec.f_elements (v i)));
            assert (forall j. j < v i + 1 ==> Spec.Utils.is_i16b 3328 (Seq.index vec.f_elements j))
          in
          vec)
  in
  vec

#pop-options

let bitwise_and_with_constant
      (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (c: i16)
     =
  let v__vec0:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun vec i ->
          let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let i:usize = i in
          (forall j. j < v i ==> Seq.index vec.f_elements j == (Seq.index v__vec0.f_elements j &. c)
          ) /\ (forall j. j >= v i ==> Seq.index vec.f_elements j == Seq.index v__vec0.f_elements j)
      )
      vec
      (fun vec i ->
          let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let i:usize = i in
          let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
            {
              vec with
              Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vec
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
                i
                ((vec.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) &. c
                  <:
                  i16)
            }
            <:
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
          in
          vec)
  in
  let _:Prims.unit =
    Spec.Utils.lemma_map_index #_ #_ #(sz 16) (fun x -> x &. c) v__vec0.f_elements;
    Seq.lemma_eq_intro vec.f_elements (Spec.Utils.map_array (fun x -> x &. c) v__vec0.f_elements)
  in
  vec

let cond_subtract_3329_ (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let v__vec0:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun vec i ->
          let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let i:usize = i in
          (forall j.
              j < v i ==>
              Seq.index vec.f_elements j ==
              (let x = Seq.index v__vec0.f_elements j in
                if x >=. 3329s then x -! 3329s else x)) /\
          (forall j. j >= v i ==> Seq.index vec.f_elements j == Seq.index v__vec0.f_elements j))
      vec
      (fun vec i ->
          let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let i:usize = i in
          if
            (vec.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) >=. 3329s
            <:
            bool
          then
            {
              vec with
              Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vec
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
                i
                ((vec.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) -! 3329s
                  <:
                  i16)
              <:
              t_Array i16 (sz 16)
            }
            <:
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
          else vec)
  in
  let _:Prims.unit =
    Spec.Utils.lemma_map_index #_
      #_
      #(sz 16)
      (fun x -> if x >=. 3329s then x -! 3329s else x)
      v__vec0.f_elements;
    Seq.lemma_eq_intro vec.f_elements
      (Spec.Utils.map_array (fun x -> if x >=. 3329s then x -! 3329s else x) v__vec0.f_elements)
  in
  let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

#push-options "--z3rlimit 150"

let montgomery_multiply_by_constant
      (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (c: i16)
     =
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun v temp_1_ ->
          let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = v in
          let _:usize = temp_1_ in
          true)
      v
      (fun v i ->
          let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = v in
          let i:usize = i in
          {
            v with
            Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
                .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
              i
              (montgomery_multiply_fe_by_fer (v
                      .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ]
                    <:
                    i16)
                  c
                <:
                i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  v

#pop-options

let multiply_by_constant (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (c: i16) =
  let v__vec0:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun vec i ->
          let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let i:usize = i in
          (forall j.
              j < v i ==> (Seq.index vec.f_elements j) == (Seq.index v__vec0.f_elements j) *. c) /\
          (forall j. j >= v i ==> (Seq.index vec.f_elements j) == (Seq.index v__vec0.f_elements j)))
      vec
      (fun vec i ->
          let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let i:usize = i in
          let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
            {
              vec with
              Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vec
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
                i
                (Core.Num.impl__i16__wrapping_mul (vec
                        .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ]
                      <:
                      i16)
                    c
                  <:
                  i16)
            }
            <:
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
          in
          vec)
  in
  let _:Prims.unit =
    Spec.Utils.lemma_map_index #_ #_ #(sz 16) (fun x -> x *. c) v__vec0.f_elements;
    Seq.lemma_eq_intro vec.f_elements (Spec.Utils.map_array (fun x -> x *. c) v__vec0.f_elements)
  in
  vec

let shift_right (v_SHIFT_BY: i32) (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let v__vec0:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun vec i ->
          let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let i:usize = i in
          (forall j.
              j < v i ==>
              Seq.index vec.f_elements j == (Seq.index v__vec0.f_elements j >>! v_SHIFT_BY)) /\
          (forall j. j >= v i ==> Seq.index vec.f_elements j == Seq.index v__vec0.f_elements j))
      vec
      (fun vec i ->
          let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec in
          let i:usize = i in
          let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
            {
              vec with
              Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vec
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
                i
                ((vec.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) >>!
                  v_SHIFT_BY
                  <:
                  i16)
            }
            <:
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
          in
          vec)
  in
  let _:Prims.unit =
    Spec.Utils.lemma_map_index #_ #_ #(sz 16) (fun x -> x >>! v_SHIFT_BY) v__vec0.f_elements;
    Seq.lemma_eq_intro vec.f_elements
      (Spec.Utils.map_array (fun x -> x >>! v_SHIFT_BY) v__vec0.f_elements)
  in
  vec

let sub (lhs rhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let v__lhs0:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = lhs in
  let lhs:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun lhs i ->
          let lhs:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = lhs in
          let i:usize = i in
          (forall j.
              j < v i ==>
              (Seq.index lhs.f_elements j) ==
              (Seq.index v__lhs0.f_elements j) -. (Seq.index rhs.f_elements j)) /\
          (forall j. j >= v i ==> (Seq.index lhs.f_elements j) == (Seq.index v__lhs0.f_elements j)))
      lhs
      (fun lhs i ->
          let lhs:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = lhs in
          let i:usize = i in
          let lhs:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
            {
              lhs with
              Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
                i
                (Core.Num.impl__i16__wrapping_sub (lhs
                        .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ]
                      <:
                      i16)
                    (rhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16)
                  <:
                  i16)
            }
            <:
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
          in
          lhs)
  in
  let _:Prims.unit =
    Spec.Utils.lemma_map2_index #_ #_ #_ #(sz 16) ( -. ) v__lhs0.f_elements rhs.f_elements;
    Seq.lemma_eq_intro lhs.f_elements (Spec.Utils.map2 ( -. ) v__lhs0.f_elements rhs.f_elements)
  in
  lhs
