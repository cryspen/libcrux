module Libcrux_ml_kem.Polynomial
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Traits in
  ()

let zeta (i: usize) =
  let result:i16 = v_ZETAS_TIMES_MONTGOMERY_R.[ i ] in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

[@@ "opaque_to_smt"]

let add_vector
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (lhs rhs: v_Vector)
     =
  let _:Prims.unit = reveal_opaque (`%add_vector_pre) (add_vector_pre #v_Vector) in
  let _:Prims.unit = reveal_opaque (`%add_vector_post) (add_vector_post #v_Vector) in
  Libcrux_ml_kem.Vector.Traits.f_add #v_Vector #FStar.Tactics.Typeclasses.solve lhs rhs

let sub_vector
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (lhs rhs: v_Vector)
     =
  let _:Prims.unit = reveal_opaque (`%sub_vector_pre) (sub_vector_pre #v_Vector) in
  let _:Prims.unit = reveal_opaque (`%sub_vector_post) (sub_vector_post #v_Vector) in
  Libcrux_ml_kem.Vector.Traits.f_sub #v_Vector #FStar.Tactics.Typeclasses.solve lhs rhs

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl':
    #v_Vector: Type0 ->
    {| i1: Core.Clone.t_Clone v_Vector |} ->
    {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  -> Core.Clone.t_Clone (t_PolynomialRingElement v_Vector)

let impl
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
     = impl' #v_Vector #i1 #i2

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1':
    #v_Vector: Type0 ->
    {| i1: Core.Marker.t_Copy v_Vector |} ->
    {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  -> Core.Marker.t_Copy (t_PolynomialRingElement v_Vector)

let impl_1
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Marker.t_Copy v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
     = impl_1' #v_Vector #i1 #i2

#push-options "--max_fuel 3 --z3rlimit 200 --ext context_pruning --z3refresh"

let add_error_reduce_helper (#v_Vector: Type0)
    {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    (error: t_Array v_Vector (sz 16))
    (coefficient_normal_form: v_Vector) : Lemma
    (requires (forall (i:nat). i < 16 ==>
        Spec.Utils.is_i16b_array_opaque (28296 - 3328)
        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array error.[ sz i ])) /\
        Spec.Utils.is_i16b_array_opaque 3328
        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array coefficient_normal_form))
    (ensures (forall (i:nat). i < 16 ==> add_vector_pre coefficient_normal_form error.[ sz i ] /\
        Spec.Utils.is_i16b_array_opaque 28296 (Libcrux_ml_kem.Vector.Traits.f_to_i16_array
        (add_vector coefficient_normal_form error.[ sz i ]))))
    =
    reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) Spec.Utils.is_i16b_array_opaque;
    reveal_opaque (`%add_vector_pre) (add_vector_pre #v_Vector);
    reveal_opaque (`%add_vector_post) (add_vector_post #v_Vector);
    reveal_opaque (`%add_vector) (add_vector #v_Vector);
    assert_norm (pow2 15 == 32768);
    assert (forall (i:nat). i < 16 ==>
            Spec.Utils.is_i16b_array (28296 - 3328)
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array error.[ sz i ]));
    assert (forall (i:nat). i < 16 ==> (forall j. j < 16 ==>
            Spec.Utils.is_intb 28296
            (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array coefficient_normal_form) j) +
                v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array error.[ sz i ]) j))));
    assert (forall (i:nat). i < 16 ==> (forall j. j < 16 ==>
            Spec.Utils.is_intb (pow2 15 - 1)
            (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array coefficient_normal_form) j) +
                v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array error.[ sz i ]) j))))

#pop-options

let add_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (myself error: t_PolynomialRingElement v_Vector)
     =
  let myself:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun myself temp_1_ ->
          let myself:t_PolynomialRingElement v_Vector = myself in
          let _:usize = temp_1_ in
          true)
      myself
      (fun myself j ->
          let myself:t_PolynomialRingElement v_Vector = myself in
          let j:usize = j in
          let coefficient_normal_form:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_montgomery_multiply_by_constant #v_Vector
              #FStar.Tactics.Typeclasses.solve
              (myself.f_coefficients.[ j ] <: v_Vector)
              1441s
          in
          let _:Prims.unit = add_error_reduce_helper error.f_coefficients coefficient_normal_form in
          let myself:t_PolynomialRingElement v_Vector =
            {
              myself with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize myself.f_coefficients
                j
                (Libcrux_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (add_vector #v_Vector
                        coefficient_normal_form
                        (error.f_coefficients.[ j ] <: v_Vector)
                      <:
                      v_Vector)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          myself)
  in
  myself

let impl_2__add_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self error: t_PolynomialRingElement v_Vector)
     =
  let self:t_PolynomialRingElement v_Vector = add_error_reduce #v_Vector self error in
  self

let add_message_error_reduce_helper (#v_Vector: Type0)
    {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    (result coefficient_normal_form: v_Vector) : Lemma
    (requires (Spec.Utils.is_i16b_array_opaque (28296 - 3328)
          (Libcrux_ml_kem.Vector.Traits.f_to_i16_array result) /\
        Spec.Utils.is_i16b_array_opaque 3328
          (Libcrux_ml_kem.Vector.Traits.f_to_i16_array coefficient_normal_form)))
    (ensures (add_vector_pre coefficient_normal_form result /\
        Spec.Utils.is_i16b_array_opaque 28296 (Libcrux_ml_kem.Vector.Traits.f_to_i16_array
          (add_vector coefficient_normal_form result))))
    =
    reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) Spec.Utils.is_i16b_array_opaque;
    reveal_opaque (`%add_vector_pre) (add_vector_pre #v_Vector);
    reveal_opaque (`%add_vector_post) (add_vector_post #v_Vector);
    assert_norm (pow2 15 == 32768)

let add_message_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (myself message result: t_PolynomialRingElement v_Vector)
     =
  let result:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun result temp_1_ ->
          let result:t_PolynomialRingElement v_Vector = result in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:t_PolynomialRingElement v_Vector = result in
          let i:usize = i in
          let coefficient_normal_form:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_montgomery_multiply_by_constant #v_Vector
              #FStar.Tactics.Typeclasses.solve
              (result.f_coefficients.[ i ] <: v_Vector)
              1441s
          in
          let tmp:v_Vector =
            add_vector #v_Vector
              (myself.f_coefficients.[ i ] <: v_Vector)
              (message.f_coefficients.[ i ] <: v_Vector)
          in
          let _:Prims.unit = add_message_error_reduce_helper tmp coefficient_normal_form in
          let tmp:v_Vector = add_vector #v_Vector coefficient_normal_form tmp in
          let result:t_PolynomialRingElement v_Vector =
            {
              result with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_coefficients
                i
                (Libcrux_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    tmp
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          result)
  in
  result

let impl_2__add_message_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self message result: t_PolynomialRingElement v_Vector)
     = add_message_error_reduce #v_Vector self message result

let add_standard_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (myself error: t_PolynomialRingElement v_Vector)
     =
  let myself:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun myself temp_1_ ->
          let myself:t_PolynomialRingElement v_Vector = myself in
          let _:usize = temp_1_ in
          true)
      myself
      (fun myself j ->
          let myself:t_PolynomialRingElement v_Vector = myself in
          let j:usize = j in
          let coefficient_normal_form:v_Vector =
            Libcrux_ml_kem.Vector.Traits.to_standard_domain #v_Vector
              (myself.f_coefficients.[ j ] <: v_Vector)
          in
          let _:Prims.unit = add_error_reduce_helper error.f_coefficients coefficient_normal_form in
          let myself:t_PolynomialRingElement v_Vector =
            {
              myself with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize myself.f_coefficients
                j
                (Libcrux_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (add_vector #v_Vector
                        coefficient_normal_form
                        (error.f_coefficients.[ j ] <: v_Vector)
                      <:
                      v_Vector)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          myself)
  in
  myself

let impl_2__add_standard_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self error: t_PolynomialRingElement v_Vector)
     =
  let self:t_PolynomialRingElement v_Vector = add_standard_error_reduce #v_Vector self error in
  self

let poly_barrett_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (myself: t_PolynomialRingElement v_Vector)
     =
  let myself:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun myself i ->
          let myself:t_PolynomialRingElement v_Vector = myself in
          let i:usize = i in
          v i < v v_VECTORS_IN_RING_ELEMENT ==>
          (forall (j: nat).
              (j >= v i /\ j < v v_VECTORS_IN_RING_ELEMENT) ==>
              Spec.Utils.is_i16b_array_opaque 28296
                (Libcrux_ml_kem.Vector.Traits.f_to_i16_array myself.f_coefficients.[ sz j ])))
      myself
      (fun myself i ->
          let myself:t_PolynomialRingElement v_Vector = myself in
          let i:usize = i in
          let myself:t_PolynomialRingElement v_Vector =
            {
              myself with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize myself.f_coefficients
                i
                (Libcrux_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (myself.f_coefficients.[ i ] <: v_Vector)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          myself)
  in
  myself

let impl_2__poly_barrett_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self: t_PolynomialRingElement v_Vector)
     =
  let self:t_PolynomialRingElement v_Vector = poly_barrett_reduce #v_Vector self in
  self

#push-options "--z3rlimit 200 --ext context_pruning"

let subtract_reduce_helper (#v_Vector: Type0)
    {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    (myself: t_Array v_Vector (sz 16))
    (coefficient_normal_form: v_Vector) : Lemma
    (requires (forall (i:nat). i < 16 ==>
        Spec.Utils.is_i16b_array_opaque (28296 - 3328)
        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array myself.[ sz i ])) /\
        Spec.Utils.is_i16b_array_opaque 3328
        (Libcrux_ml_kem.Vector.Traits.f_to_i16_array coefficient_normal_form))
    (ensures (forall (i:nat). i < 16 ==> sub_vector_pre myself.[ sz i ] coefficient_normal_form /\
        Spec.Utils.is_i16b_array_opaque 28296 (Libcrux_ml_kem.Vector.Traits.f_to_i16_array
        (sub_vector myself.[ sz i ] coefficient_normal_form))))
    =
    reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) Spec.Utils.is_i16b_array_opaque;
    reveal_opaque (`%sub_vector_pre) (sub_vector_pre #v_Vector);
    reveal_opaque (`%sub_vector_post) (sub_vector_post #v_Vector);
    assert_norm (pow2 15 == 32768);
    assert (forall (i:nat). i < 16 ==>
            Spec.Utils.is_i16b_array (28296 - 3328)
            (Libcrux_ml_kem.Vector.Traits.f_to_i16_array myself.[ sz i ]));
    assert (forall (i:nat). i < 16 ==> (forall j. j < 16 ==>
            Spec.Utils.is_intb 28296
            (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array myself.[ sz i ]) j) -
                v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array coefficient_normal_form) j))));
    assert (forall (i:nat). i < 16 ==> (forall j. j < 16 ==>
            Spec.Utils.is_intb (pow2 15 - 1)
            (v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array myself.[ sz i ]) j) -
                v (Seq.index (Libcrux_ml_kem.Vector.Traits.f_to_i16_array coefficient_normal_form) j))))

#pop-options

let subtract_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (myself b: t_PolynomialRingElement v_Vector)
     =
  let b:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun b temp_1_ ->
          let b:t_PolynomialRingElement v_Vector = b in
          let _:usize = temp_1_ in
          true)
      b
      (fun b i ->
          let b:t_PolynomialRingElement v_Vector = b in
          let i:usize = i in
          let coefficient_normal_form:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_montgomery_multiply_by_constant #v_Vector
              #FStar.Tactics.Typeclasses.solve
              (b.f_coefficients.[ i ] <: v_Vector)
              1441s
          in
          let _:Prims.unit = subtract_reduce_helper myself.f_coefficients coefficient_normal_form in
          let b:t_PolynomialRingElement v_Vector =
            {
              b with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize b.f_coefficients
                i
                (Libcrux_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (sub_vector #v_Vector
                        (myself.f_coefficients.[ i ] <: v_Vector)
                        coefficient_normal_form
                      <:
                      v_Vector)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          b)
  in
  b

let impl_2__subtract_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self b: t_PolynomialRingElement v_Vector)
     = subtract_reduce #v_Vector self b

let impl_2__ZERO
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (_: Prims.unit)
     =
  {
    f_coefficients
    =
    Rust_primitives.Hax.repeat (Libcrux_ml_kem.Vector.Traits.f_ZERO #v_Vector
          #FStar.Tactics.Typeclasses.solve
          ()
        <:
        v_Vector)
      (sz 16)
  }
  <:
  t_PolynomialRingElement v_Vector

let v_ZERO
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (_: Prims.unit)
     =
  {
    f_coefficients
    =
    Rust_primitives.Hax.repeat (Libcrux_ml_kem.Vector.Traits.f_ZERO #v_Vector
          #FStar.Tactics.Typeclasses.solve
          ()
        <:
        v_Vector)
      (sz 16)
  }
  <:
  t_PolynomialRingElement v_Vector

let from_i16_array
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (a: t_Slice i16)
     =
  let result:t_PolynomialRingElement v_Vector = v_ZERO #v_Vector () in
  let result:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun result temp_1_ ->
          let result:t_PolynomialRingElement v_Vector = result in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:t_PolynomialRingElement v_Vector = result in
          let i:usize = i in
          {
            result with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_coefficients
              i
              (Libcrux_ml_kem.Vector.Traits.f_from_i16_array #v_Vector
                  #FStar.Tactics.Typeclasses.solve
                  (a.[ {
                        Core.Ops.Range.f_start = i *! sz 16 <: usize;
                        Core.Ops.Range.f_end = (i +! sz 1 <: usize) *! sz 16 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice i16)
                <:
                v_Vector)
            <:
            t_Array v_Vector (sz 16)
          }
          <:
          t_PolynomialRingElement v_Vector)
  in
  result

let impl_2__from_i16_array
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (a: t_Slice i16)
     = from_i16_array #v_Vector a

#push-options "--z3rlimit 200 --ext context_pruning"

let ntt_multiply
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (myself rhs: t_PolynomialRingElement v_Vector)
     =
  let out:t_PolynomialRingElement v_Vector = v_ZERO #v_Vector () in
  let out:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun out temp_1_ ->
          let out:t_PolynomialRingElement v_Vector = out in
          let _:usize = temp_1_ in
          true)
      out
      (fun out i ->
          let out:t_PolynomialRingElement v_Vector = out in
          let i:usize = i in
          {
            out with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_coefficients
              i
              (Libcrux_ml_kem.Vector.Traits.f_ntt_multiply #v_Vector
                  #FStar.Tactics.Typeclasses.solve
                  (myself.f_coefficients.[ i ] <: v_Vector)
                  (rhs.f_coefficients.[ i ] <: v_Vector)
                  (zeta (sz 64 +! (sz 4 *! i <: usize) <: usize) <: i16)
                  (zeta ((sz 64 +! (sz 4 *! i <: usize) <: usize) +! sz 1 <: usize) <: i16)
                  (zeta ((sz 64 +! (sz 4 *! i <: usize) <: usize) +! sz 2 <: usize) <: i16)
                  (zeta ((sz 64 +! (sz 4 *! i <: usize) <: usize) +! sz 3 <: usize) <: i16)
                <:
                v_Vector)
            <:
            t_Array v_Vector (sz 16)
          }
          <:
          t_PolynomialRingElement v_Vector)
  in
  out

#pop-options

let impl_2__ntt_multiply
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self rhs: t_PolynomialRingElement v_Vector)
     = ntt_multiply #v_Vector self rhs

let add_to_ring_element
      (#v_Vector: Type0)
      (v_K: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (myself rhs: t_PolynomialRingElement v_Vector)
     =
  let v__myself:t_Array v_Vector (sz 16) = myself.f_coefficients in
  let myself:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #v_Vector (myself.f_coefficients <: t_Slice v_Vector) <: usize)
      (fun myself i ->
          let myself:t_PolynomialRingElement v_Vector = myself in
          let i:usize = i in
          (v i < v (Core.Slice.impl__len myself.f_coefficients) ==>
            (forall (j: nat).
                (j >= v i /\ j < v (Core.Slice.impl__len myself.f_coefficients)) ==>
                myself.f_coefficients.[ sz j ] == v__myself.[ sz j ] /\
                add_vector_pre myself.f_coefficients.[ sz j ] rhs.f_coefficients.[ sz j ])) /\
          (forall (j: nat).
              j < v i ==>
              add_vector_post myself.f_coefficients.[ sz j ]
                v__myself.[ sz j ]
                rhs.f_coefficients.[ sz j ]))
      myself
      (fun myself i ->
          let myself:t_PolynomialRingElement v_Vector = myself in
          let i:usize = i in
          let myself:t_PolynomialRingElement v_Vector =
            {
              myself with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize myself.f_coefficients
                i
                (add_vector #v_Vector
                    (myself.f_coefficients.[ i ] <: v_Vector)
                    (rhs.f_coefficients.[ i ] <: v_Vector)
                  <:
                  v_Vector)
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          myself)
  in
  myself

let impl_2__add_to_ring_element
      (#v_Vector: Type0)
      (v_K: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self rhs: t_PolynomialRingElement v_Vector)
     =
  let self:t_PolynomialRingElement v_Vector = add_to_ring_element #v_Vector v_K self rhs in
  self
