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
      (mk_usize 16)
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
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
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
                        Core.Ops.Range.f_start = i *! mk_usize 16 <: usize;
                        Core.Ops.Range.f_end = (i +! mk_usize 1 <: usize) *! mk_usize 16 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice i16)
                <:
                v_Vector)
            <:
            t_Array v_Vector (mk_usize 16)
          }
          <:
          t_PolynomialRingElement v_Vector)
  in
  result

let to_i16_array
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: t_PolynomialRingElement v_Vector)
      (out: t_Slice i16)
     =
  let e_out_len:usize = Core.Slice.impl__len #i16 out in
  let out:t_Slice i16 =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #v_Vector (re.f_coefficients <: t_Slice v_Vector) <: usize)
      (fun out e_i ->
          let out:t_Slice i16 = out in
          let e_i:usize = e_i in
          (Core.Slice.impl__len #i16 out <: usize) =. e_out_len <: bool)
      out
      (fun out i ->
          let out:t_Slice i16 = out in
          let i:usize = i in
          let out:t_Slice i16 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
              ({
                  Core.Ops.Range.f_start = i *! mk_usize 16 <: usize;
                  Core.Ops.Range.f_end = (i +! mk_usize 1 <: usize) *! mk_usize 16 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #i16
                  (out.[ {
                        Core.Ops.Range.f_start = i *! mk_usize 16 <: usize;
                        Core.Ops.Range.f_end = (i +! mk_usize 1 <: usize) *! mk_usize 16 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice i16)
                  (Libcrux_ml_kem.Vector.Traits.f_to_i16_array #v_Vector
                      #FStar.Tactics.Typeclasses.solve
                      (re.f_coefficients.[ i ] <: v_Vector)
                    <:
                    t_Slice i16)
                <:
                t_Slice i16)
          in
          out)
  in
  out

let from_bytes
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (bytes: t_Slice u8)
     =
  let result:t_PolynomialRingElement v_Vector = v_ZERO #v_Vector () in
  let result:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
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
              (Libcrux_ml_kem.Vector.Traits.f_from_bytes #v_Vector
                  #FStar.Tactics.Typeclasses.solve
                  (bytes.[ {
                        Core.Ops.Range.f_start = i *! mk_usize 32 <: usize;
                        Core.Ops.Range.f_end = (i +! mk_usize 1 <: usize) *! mk_usize 32 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                v_Vector)
            <:
            t_Array v_Vector (mk_usize 16)
          }
          <:
          t_PolynomialRingElement v_Vector)
  in
  result

let to_bytes
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: t_PolynomialRingElement v_Vector)
      (out: t_Slice u8)
     =
  let e_out_len:usize = Core.Slice.impl__len #u8 out in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #v_Vector (re.f_coefficients <: t_Slice v_Vector) <: usize)
      (fun out e_i ->
          let out:t_Slice u8 = out in
          let e_i:usize = e_i in
          (Core.Slice.impl__len #u8 out <: usize) =. e_out_len <: bool)
      out
      (fun out i ->
          let out:t_Slice u8 = out in
          let i:usize = i in
          let out:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
              ({
                  Core.Ops.Range.f_start = i *! mk_usize 32 <: usize;
                  Core.Ops.Range.f_end = (i +! mk_usize 1 <: usize) *! mk_usize 32 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Libcrux_ml_kem.Vector.Traits.f_to_bytes #v_Vector
                  #FStar.Tactics.Typeclasses.solve
                  (re.f_coefficients.[ i ] <: v_Vector)
                  (out.[ {
                        Core.Ops.Range.f_start = i *! mk_usize 32 <: usize;
                        Core.Ops.Range.f_end = (i +! mk_usize 1 <: usize) *! mk_usize 32 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          out)
  in
  out

#push-options "--z3rlimit 300"

let add_to_ring_element
      (#v_Vector: Type0)
      (v_K: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (myself rhs: t_PolynomialRingElement v_Vector)
     =
  let e_myself:t_Array v_Vector (mk_usize 16) = myself.f_coefficients in
  let myself:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #v_Vector (myself.f_coefficients <: t_Slice v_Vector) <: usize)
      (fun myself i ->
          let myself:t_PolynomialRingElement v_Vector = myself in
          let i:usize = i in
          v i <= v v_VECTORS_IN_RING_ELEMENT /\
          (forall (j: nat).
              (j >= v i /\ j < v v_VECTORS_IN_RING_ELEMENT) ==>
              (let _myself_j = i1.f_to_i16_array (e_myself.[ sz j ]) in
                let myself_j = i1.f_to_i16_array (myself.f_coefficients.[ sz j ]) in
                let rhs_j = i1.f_to_i16_array (rhs.f_coefficients.[ sz j ]) in
                myself_j == _myself_j /\ Libcrux_ml_kem.Vector.Traits.Spec.add_pre myself_j rhs_j)) /\
          (forall (j: nat).
              j < v i ==>
              (let _myself_j = i1.f_to_i16_array (e_myself.[ sz j ]) in
                let myself_j = i1.f_to_i16_array (myself.f_coefficients.[ sz j ]) in
                let rhs_j = i1.f_to_i16_array (rhs.f_coefficients.[ sz j ]) in
                Libcrux_ml_kem.Vector.Traits.Spec.add_post _myself_j rhs_j myself_j)))
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
                (Libcrux_ml_kem.Vector.Traits.f_add #v_Vector
                    #FStar.Tactics.Typeclasses.solve
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

#pop-options

let poly_barrett_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (myself: t_PolynomialRingElement v_Vector)
     =
  let e_myself:t_Array v_Vector (mk_usize 16) = myself.f_coefficients in
  let myself:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun myself i ->
          let myself:t_PolynomialRingElement v_Vector = myself in
          let i:usize = i in
          (forall j. j < v i ==> is_bounded_vector 3328 myself.f_coefficients.[ sz j ]) /\
          (forall j. (j >= v i /\ j < 16) ==> myself.f_coefficients.[ sz j ] == e_myself.[ sz j ]))
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

#push-options "--z3rlimit 300"

let subtract_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (myself b: t_PolynomialRingElement v_Vector)
     =
  let e_b:t_Array v_Vector (mk_usize 16) = b.f_coefficients in
  let b:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun b i ->
          let b:t_PolynomialRingElement v_Vector = b in
          let i:usize = i in
          (forall j. j < v i ==> is_bounded_vector 3328 b.f_coefficients.[ sz j ]) /\
          (forall j. (j >= v i /\ j < 16) ==> b.f_coefficients.[ sz j ] == e_b.[ sz j ]))
      b
      (fun b i ->
          let b:t_PolynomialRingElement v_Vector = b in
          let i:usize = i in
          let _:Prims.unit =
            assert (v i < 16);
            assert_norm (1441 < pow2 15);
            assert_norm (1664 < pow2 15);
            assert_norm (mk_i16 1441 <. mk_i16 1664);
            assert (Spec.Utils.is_i16b 1664 (mk_i16 1441))
          in
          let coefficient_normal_form:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_montgomery_multiply_by_constant #v_Vector
              #FStar.Tactics.Typeclasses.solve
              (b.f_coefficients.[ i ] <: v_Vector)
              (mk_i16 1441)
          in
          let _:Prims.unit =
            assert (is_bounded_vector 3328 coefficient_normal_form);
            assert (is_bounded_vector (pow2 12 - 1) (myself.f_coefficients.[ i ]));
            assert_norm (pow2 12 - 1 == 4095);
            Spec.Utils.lemma_sub_intb_forall 4095 3328;
            assert (forall j.
                  Spec.Utils.is_intb 7423
                    (v (Seq.index (i1.f_to_i16_array myself.f_coefficients.[ i ]) j) -
                      v (Seq.index (i1.f_to_i16_array coefficient_normal_form) j)));
            assert_norm (7423 <= pow2 15 - 1);
            Spec.Utils.lemma_intb_le 7423 (pow2 15 - 1);
            Spec.Utils.lemma_intb_le 7423 28296;
            assert (forall j.
                  Spec.Utils.is_intb (pow2 15 - 1)
                    (v (Seq.index (i1.f_to_i16_array myself.f_coefficients.[ i ]) j) -
                      v (Seq.index (i1.f_to_i16_array coefficient_normal_form) j)));
            assert (forall j.
                  Spec.Utils.is_intb 28296
                    (v (Seq.index (i1.f_to_i16_array myself.f_coefficients.[ i ]) j) -
                      v (Seq.index (i1.f_to_i16_array coefficient_normal_form) j)))
          in
          let diff:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_sub #v_Vector
              #FStar.Tactics.Typeclasses.solve
              (myself.f_coefficients.[ i ] <: v_Vector)
              coefficient_normal_form
          in
          let _:Prims.unit = assert (is_bounded_vector 28296 diff) in
          let red:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
              #FStar.Tactics.Typeclasses.solve
              diff
          in
          let _:Prims.unit = assert (is_bounded_vector 3328 red) in
          let b:t_PolynomialRingElement v_Vector =
            {
              b with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize b.f_coefficients i red
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          let _:Prims.unit =
            assert (forall j. (j > v i /\ j < 16) ==> b.f_coefficients.[ sz j ] == e_b.[ sz j ]);
            assert (forall j. j < v i ==> is_bounded_vector 3328 b.f_coefficients.[ sz j ]);
            assert (b.f_coefficients.[ i ] == red);
            assert (forall j. j <= v i ==> is_bounded_vector 3328 b.f_coefficients.[ sz j ])
          in
          b)
  in
  b

#pop-options

#push-options "--admit_smt_queries true"

let add_message_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (myself message result: t_PolynomialRingElement v_Vector)
     =
  let result:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
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
              (mk_i16 1441)
          in
          let tmp:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_add #v_Vector
              #FStar.Tactics.Typeclasses.solve
              (myself.f_coefficients.[ i ] <: v_Vector)
              (message.f_coefficients.[ i ] <: v_Vector)
          in
          let tmp:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_add #v_Vector
              #FStar.Tactics.Typeclasses.solve
              coefficient_normal_form
              tmp
          in
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

#pop-options

#push-options "--z3rlimit 300"

let add_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (myself error: t_PolynomialRingElement v_Vector)
     =
  let e_myself:t_Array v_Vector (mk_usize 16) = myself.f_coefficients in
  let myself:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun myself i ->
          let myself:t_PolynomialRingElement v_Vector = myself in
          let i:usize = i in
          (forall j. j < v i ==> is_bounded_vector 3328 myself.f_coefficients.[ sz j ]) /\
          (forall j. (j >= v i /\ j < 16) ==> myself.f_coefficients.[ sz j ] == e_myself.[ sz j ]))
      myself
      (fun myself j ->
          let myself:t_PolynomialRingElement v_Vector = myself in
          let j:usize = j in
          let coefficient_normal_form:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_montgomery_multiply_by_constant #v_Vector
              #FStar.Tactics.Typeclasses.solve
              (myself.f_coefficients.[ j ] <: v_Vector)
              (mk_i16 1441)
          in
          let _:Prims.unit =
            assert (is_bounded_vector 3328 coefficient_normal_form);
            assert (is_bounded_vector 7 (error.f_coefficients.[ j ]));
            Spec.Utils.lemma_add_intb_forall 3328 7;
            assert (forall i.
                  Spec.Utils.is_intb 3335
                    (v (Seq.index (i1.f_to_i16_array coefficient_normal_form) i) +
                      v (Seq.index (i1.f_to_i16_array error.f_coefficients.[ j ]) i)));
            assert_norm (3335 <= pow2 15 - 1);
            Spec.Utils.lemma_intb_le 3335 (pow2 15 - 1);
            Spec.Utils.lemma_intb_le 3335 28296;
            assert (forall i.
                  Spec.Utils.is_intb (pow2 15 - 1)
                    (v (Seq.index (i1.f_to_i16_array coefficient_normal_form) i) +
                      v (Seq.index (i1.f_to_i16_array error.f_coefficients.[ j ]) i)));
            assert (forall i.
                  Spec.Utils.is_intb 28296
                    (v (Seq.index (i1.f_to_i16_array coefficient_normal_form) i) +
                      v (Seq.index (i1.f_to_i16_array error.f_coefficients.[ j ]) i)))
          in
          let sum:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_add #v_Vector
              #FStar.Tactics.Typeclasses.solve
              coefficient_normal_form
              (error.f_coefficients.[ j ] <: v_Vector)
          in
          let _:Prims.unit = assert (is_bounded_vector 3335 sum) in
          let red:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
              #FStar.Tactics.Typeclasses.solve
              sum
          in
          let _:Prims.unit = assert (is_bounded_vector 3328 red) in
          let myself:t_PolynomialRingElement v_Vector =
            {
              myself with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize myself.f_coefficients
                j
                red
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          let _:Prims.unit =
            assert (forall i.
                  (i > v j /\ i < 16) ==> myself.f_coefficients.[ sz i ] == e_myself.[ sz i ]);
            assert (forall i. i < v j ==> is_bounded_vector 3328 myself.f_coefficients.[ sz i ]);
            assert (myself.f_coefficients.[ j ] == red);
            assert (forall i. i <= v j ==> is_bounded_vector 3328 myself.f_coefficients.[ sz i ])
          in
          myself)
  in
  myself

#pop-options

let to_standard_domain
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_T)
      (vector: v_T)
     =
  Libcrux_ml_kem.Vector.Traits.f_montgomery_multiply_by_constant #v_T
    #FStar.Tactics.Typeclasses.solve
    vector
    Libcrux_ml_kem.Vector.Traits.v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS

#push-options "--z3rlimit 300"

let add_standard_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (myself error: t_PolynomialRingElement v_Vector)
     =
  let e_myself:t_Array v_Vector (mk_usize 16) = myself.f_coefficients in
  let myself:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun myself i ->
          let myself:t_PolynomialRingElement v_Vector = myself in
          let i:usize = i in
          (forall j. j < v i ==> is_bounded_vector 3328 myself.f_coefficients.[ sz j ]) /\
          (forall j. (j >= v i /\ j < 16) ==> myself.f_coefficients.[ sz j ] == e_myself.[ sz j ]))
      myself
      (fun myself j ->
          let myself:t_PolynomialRingElement v_Vector = myself in
          let j:usize = j in
          let coefficient_normal_form:v_Vector =
            to_standard_domain #v_Vector (myself.f_coefficients.[ j ] <: v_Vector)
          in
          let _:Prims.unit =
            assert (is_bounded_vector 3328 coefficient_normal_form);
            assert (is_bounded_vector 3328 (error.f_coefficients.[ j ]));
            Spec.Utils.lemma_add_intb_forall 3328 3328;
            assert (forall i.
                  Spec.Utils.is_intb 6656
                    (v (Seq.index (i1.f_to_i16_array coefficient_normal_form) i) +
                      v (Seq.index (i1.f_to_i16_array error.f_coefficients.[ j ]) i)));
            assert_norm (6656 <= pow2 15 - 1);
            Spec.Utils.lemma_intb_le 6656 (pow2 15 - 1);
            Spec.Utils.lemma_intb_le 6656 28296;
            assert (forall i.
                  Spec.Utils.is_intb (pow2 15 - 1)
                    (v (Seq.index (i1.f_to_i16_array coefficient_normal_form) i) +
                      v (Seq.index (i1.f_to_i16_array error.f_coefficients.[ j ]) i)));
            assert (forall i.
                  Spec.Utils.is_intb 28296
                    (v (Seq.index (i1.f_to_i16_array coefficient_normal_form) i) +
                      v (Seq.index (i1.f_to_i16_array error.f_coefficients.[ j ]) i)))
          in
          let sum:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_add #v_Vector
              #FStar.Tactics.Typeclasses.solve
              coefficient_normal_form
              (error.f_coefficients.[ j ] <: v_Vector)
          in
          let _:Prims.unit = assert (is_bounded_vector 6656 sum) in
          let red:v_Vector =
            Libcrux_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
              #FStar.Tactics.Typeclasses.solve
              sum
          in
          let _:Prims.unit = assert (is_bounded_vector 3328 red) in
          let myself:t_PolynomialRingElement v_Vector =
            {
              myself with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize myself.f_coefficients
                j
                red
            }
            <:
            t_PolynomialRingElement v_Vector
          in
          let _:Prims.unit =
            assert (forall i.
                  (i > v j /\ i < 16) ==> myself.f_coefficients.[ sz i ] == e_myself.[ sz i ]);
            assert (forall i. i < v j ==> is_bounded_vector 3328 myself.f_coefficients.[ sz i ]);
            assert (myself.f_coefficients.[ j ] == red);
            assert (forall i. i <= v j ==> is_bounded_vector 3328 myself.f_coefficients.[ sz i ])
          in
          myself)
  in
  myself

#pop-options

#push-options "--admit_smt_queries true"

let ntt_multiply
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (myself rhs: t_PolynomialRingElement v_Vector)
     =
  let out:t_PolynomialRingElement v_Vector = v_ZERO #v_Vector () in
  let out:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
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
                  (zeta (mk_usize 64 +! (mk_usize 4 *! i <: usize) <: usize) <: i16)
                  (zeta ((mk_usize 64 +! (mk_usize 4 *! i <: usize) <: usize) +! mk_usize 1 <: usize
                      )
                    <:
                    i16)
                  (zeta ((mk_usize 64 +! (mk_usize 4 *! i <: usize) <: usize) +! mk_usize 2 <: usize
                      )
                    <:
                    i16)
                  (zeta ((mk_usize 64 +! (mk_usize 4 *! i <: usize) <: usize) +! mk_usize 3 <: usize
                      )
                    <:
                    i16)
                <:
                v_Vector)
            <:
            t_Array v_Vector (mk_usize 16)
          }
          <:
          t_PolynomialRingElement v_Vector)
  in
  out

#pop-options

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
      (mk_usize 16)
  }
  <:
  t_PolynomialRingElement v_Vector

let impl_2__add_message_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self message result: t_PolynomialRingElement v_Vector)
     = add_message_error_reduce #v_Vector self message result

let impl_2__ntt_multiply
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self rhs: t_PolynomialRingElement v_Vector)
     = ntt_multiply #v_Vector self rhs

let impl_2__num_bytes
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (_: Prims.unit)
     = v_VECTORS_IN_RING_ELEMENT *! mk_usize 32

let vec_len_bytes
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (_: Prims.unit)
     = v_K *! (impl_2__num_bytes #v_Vector () <: usize)

let impl_2__from_i16_array
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (a: t_Slice i16)
     = from_i16_array #v_Vector a

let impl_2__to_i16_array
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self: t_PolynomialRingElement v_Vector)
      (out: t_Slice i16)
     =
  let out:t_Slice i16 = to_i16_array #v_Vector self out in
  out

let impl_2__from_bytes
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (bytes: t_Slice u8)
     = from_bytes #v_Vector bytes

let vec_from_bytes
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (bytes: t_Slice u8)
      (out: t_Slice (t_PolynomialRingElement v_Vector))
     =
  let e_out_len:usize = Core.Slice.impl__len #(t_PolynomialRingElement v_Vector) out in
  let re_bytes:usize = impl_2__num_bytes #v_Vector () in
  let out:t_Slice (t_PolynomialRingElement v_Vector) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #(t_PolynomialRingElement v_Vector) out <: usize)
      (fun out e_i ->
          let out:t_Slice (t_PolynomialRingElement v_Vector) = out in
          let e_i:usize = e_i in
          (Core.Slice.impl__len #(t_PolynomialRingElement v_Vector) out <: usize) =. e_out_len
          <:
          bool)
      out
      (fun out i ->
          let out:t_Slice (t_PolynomialRingElement v_Vector) = out in
          let i:usize = i in
          let out:t_Slice (t_PolynomialRingElement v_Vector) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
              i
              (impl_2__from_bytes #v_Vector
                  (bytes.[ { Core.Ops.Range.f_start = i *! re_bytes <: usize }
                      <:
                      Core.Ops.Range.t_RangeFrom usize ]
                    <:
                    t_Slice u8)
                <:
                t_PolynomialRingElement v_Vector)
          in
          out)
  in
  out

let impl_2__to_bytes
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self: t_PolynomialRingElement v_Vector)
      (out: t_Slice u8)
     =
  let out:t_Slice u8 = to_bytes #v_Vector self out in
  out

let vec_to_bytes
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re: t_Slice (t_PolynomialRingElement v_Vector))
      (out: t_Slice u8)
     =
  let e_out_len:usize = Core.Slice.impl__len #u8 out in
  let re_bytes:usize = impl_2__num_bytes #v_Vector () in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #(t_PolynomialRingElement v_Vector) re <: usize)
      (fun out e_i ->
          let out:t_Slice u8 = out in
          let e_i:usize = e_i in
          (Core.Slice.impl__len #u8 out <: usize) =. e_out_len <: bool)
      out
      (fun out i ->
          let out:t_Slice u8 = out in
          let i:usize = i in
          let out:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
              ({ Core.Ops.Range.f_start = i *! re_bytes <: usize }
                <:
                Core.Ops.Range.t_RangeFrom usize)
              (impl_2__to_bytes #v_Vector
                  (re.[ i ] <: t_PolynomialRingElement v_Vector)
                  (out.[ { Core.Ops.Range.f_start = i *! re_bytes <: usize }
                      <:
                      Core.Ops.Range.t_RangeFrom usize ]
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          out)
  in
  out

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

let impl_2__poly_barrett_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self: t_PolynomialRingElement v_Vector)
     =
  let self:t_PolynomialRingElement v_Vector = poly_barrett_reduce #v_Vector self in
  self

let impl_2__subtract_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self b: t_PolynomialRingElement v_Vector)
     = subtract_reduce #v_Vector self b

let impl_2__add_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self error: t_PolynomialRingElement v_Vector)
     =
  let self:t_PolynomialRingElement v_Vector = add_error_reduce #v_Vector self error in
  self

let impl_2__add_standard_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self error: t_PolynomialRingElement v_Vector)
     =
  let self:t_PolynomialRingElement v_Vector = add_standard_error_reduce #v_Vector self error in
  self
