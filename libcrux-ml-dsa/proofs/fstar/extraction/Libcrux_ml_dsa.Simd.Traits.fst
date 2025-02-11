module Libcrux_ml_dsa.Simd.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Hax_lib.Abstraction in
  let open Hax_lib.Prop in
  ()

let int_is_i32 (i: Hax_lib.Int.t_Int) =
  i <=
  (Hax_lib.Abstraction.f_lift #i32 #FStar.Tactics.Typeclasses.solve Core.Num.impl_i32__MAX
    <:
    Hax_lib.Int.t_Int) &&
  i >=
  (Hax_lib.Abstraction.f_lift #i32 #FStar.Tactics.Typeclasses.solve Core.Num.impl_i32__MIN
    <:
    Hax_lib.Int.t_Int)

let add_pre (lhs rhs: t_Array i32 (mk_usize 8)) =
  Hax_lib.Prop.v_forall #usize
    #Hax_lib.Prop.t_Prop
    (fun i ->
        let i:usize = i in
        Hax_lib.Prop.implies #bool
          #bool
          (i <. v_COEFFICIENTS_IN_SIMD_UNIT <: bool)
          (fun temp_0_ ->
              let _:Prims.unit = temp_0_ in
              int_is_i32 ((Hax_lib.Abstraction.f_lift #i32
                      #FStar.Tactics.Typeclasses.solve
                      (lhs.[ i ] <: i32)
                    <:
                    Hax_lib.Int.t_Int) +
                  (Hax_lib.Abstraction.f_lift #i32
                      #FStar.Tactics.Typeclasses.solve
                      (rhs.[ i ] <: i32)
                    <:
                    Hax_lib.Int.t_Int)
                  <:
                  Hax_lib.Int.t_Int)
              <:
              bool)
        <:
        Hax_lib.Prop.t_Prop)

let add_post (lhs rhs future_lhs: t_Array i32 (mk_usize 8)) =
  Hax_lib.Prop.v_forall #usize
    #Hax_lib.Prop.t_Prop
    (fun i ->
        let i:usize = i in
        Hax_lib.Prop.implies #bool
          #bool
          (i <. v_COEFFICIENTS_IN_SIMD_UNIT <: bool)
          (fun temp_0_ ->
              let _:Prims.unit = temp_0_ in
              (Hax_lib.Abstraction.f_lift #i32
                  #FStar.Tactics.Typeclasses.solve
                  (future_lhs.[ i ] <: i32)
                <:
                Hax_lib.Int.t_Int) =
              ((Hax_lib.Abstraction.f_lift #i32 #FStar.Tactics.Typeclasses.solve (lhs.[ i ] <: i32)
                  <:
                  Hax_lib.Int.t_Int) +
                (Hax_lib.Abstraction.f_lift #i32 #FStar.Tactics.Typeclasses.solve (rhs.[ i ] <: i32)
                  <:
                  Hax_lib.Int.t_Int)
                <:
                Hax_lib.Int.t_Int)
              <:
              bool)
        <:
        Hax_lib.Prop.t_Prop)

let sub_pre (lhs rhs: t_Array i32 (mk_usize 8)) =
  Hax_lib.Prop.v_forall #usize
    #Hax_lib.Prop.t_Prop
    (fun i ->
        let i:usize = i in
        Hax_lib.Prop.implies #bool
          #bool
          (i <. v_COEFFICIENTS_IN_SIMD_UNIT <: bool)
          (fun temp_0_ ->
              let _:Prims.unit = temp_0_ in
              int_is_i32 ((Hax_lib.Abstraction.f_lift #i32
                      #FStar.Tactics.Typeclasses.solve
                      (lhs.[ i ] <: i32)
                    <:
                    Hax_lib.Int.t_Int) -
                  (Hax_lib.Abstraction.f_lift #i32
                      #FStar.Tactics.Typeclasses.solve
                      (rhs.[ i ] <: i32)
                    <:
                    Hax_lib.Int.t_Int)
                  <:
                  Hax_lib.Int.t_Int)
              <:
              bool)
        <:
        Hax_lib.Prop.t_Prop)

let sub_post (lhs rhs future_lhs: t_Array i32 (mk_usize 8)) =
  Hax_lib.Prop.v_forall #usize
    #Hax_lib.Prop.t_Prop
    (fun i ->
        let i:usize = i in
        Hax_lib.Prop.implies #bool
          #bool
          (i <. v_COEFFICIENTS_IN_SIMD_UNIT <: bool)
          (fun temp_0_ ->
              let _:Prims.unit = temp_0_ in
              (Hax_lib.Abstraction.f_lift #i32
                  #FStar.Tactics.Typeclasses.solve
                  (future_lhs.[ i ] <: i32)
                <:
                Hax_lib.Int.t_Int) =
              ((Hax_lib.Abstraction.f_lift #i32 #FStar.Tactics.Typeclasses.solve (lhs.[ i ] <: i32)
                  <:
                  Hax_lib.Int.t_Int) -
                (Hax_lib.Abstraction.f_lift #i32 #FStar.Tactics.Typeclasses.solve (rhs.[ i ] <: i32)
                  <:
                  Hax_lib.Int.t_Int)
                <:
                Hax_lib.Int.t_Int)
              <:
              bool)
        <:
        Hax_lib.Prop.t_Prop)
