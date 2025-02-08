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

#push-options "--admit_smt_queries true"

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

#pop-options

#push-options "--admit_smt_queries true"

let add_to_ring_element
      (#v_Vector: Type0)
      (v_K: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (myself rhs: t_PolynomialRingElement v_Vector)
     =
  let myself:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #v_Vector (myself.f_coefficients <: t_Slice v_Vector) <: usize)
      (fun myself temp_1_ ->
          let myself:t_PolynomialRingElement v_Vector = myself in
          let _:usize = temp_1_ in
          true)
      myself
      (fun myself i ->
          let myself:t_PolynomialRingElement v_Vector = myself in
          let i:usize = i in
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
            <:
            t_Array v_Vector (mk_usize 16)
          }
          <:
          t_PolynomialRingElement v_Vector)
  in
  myself

#pop-options

#push-options "--admit_smt_queries true"

let poly_barrett_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (myself: t_PolynomialRingElement v_Vector)
     =
  let myself:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_VECTORS_IN_RING_ELEMENT
      (fun myself temp_1_ ->
          let myself:t_PolynomialRingElement v_Vector = myself in
          let _:usize = temp_1_ in
          true)
      myself
      (fun myself i ->
          let myself:t_PolynomialRingElement v_Vector = myself in
          let i:usize = i in
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
            <:
            t_Array v_Vector (mk_usize 16)
          }
          <:
          t_PolynomialRingElement v_Vector)
  in
  myself

#pop-options

#push-options "--admit_smt_queries true"

let subtract_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (myself b: t_PolynomialRingElement v_Vector)
     =
  let b:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
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
              (mk_i16 1441)
          in
          let b:t_PolynomialRingElement v_Vector =
            {
              b with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize b.f_coefficients
                i
                (Libcrux_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (Libcrux_ml_kem.Vector.Traits.f_sub #v_Vector
                        #FStar.Tactics.Typeclasses.solve
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

#push-options "--admit_smt_queries true"

let add_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (myself error: t_PolynomialRingElement v_Vector)
     =
  let myself:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
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
              (mk_i16 1441)
          in
          let myself:t_PolynomialRingElement v_Vector =
            {
              myself with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize myself.f_coefficients
                j
                (Libcrux_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (Libcrux_ml_kem.Vector.Traits.f_add #v_Vector
                        #FStar.Tactics.Typeclasses.solve
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

#pop-options

#push-options "--admit_smt_queries true"

let add_standard_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (myself error: t_PolynomialRingElement v_Vector)
     =
  let myself:t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
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
          let myself:t_PolynomialRingElement v_Vector =
            {
              myself with
              f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize myself.f_coefficients
                j
                (Libcrux_ml_kem.Vector.Traits.f_barrett_reduce #v_Vector
                    #FStar.Tactics.Typeclasses.solve
                    (Libcrux_ml_kem.Vector.Traits.f_add #v_Vector
                        #FStar.Tactics.Typeclasses.solve
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

let impl_2__add_message_error_reduce
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (self message result: t_PolynomialRingElement v_Vector)
     = add_message_error_reduce #v_Vector self message result

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
