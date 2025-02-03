module Libcrux_ml_dsa.Simd.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let int_is_i32 (i: Hax_lib.Int.t_Int) =
  i <= (Rust_primitives.Hax.Int.from_machine Core.Num.impl_i32__MAX <: Hax_lib.Int.t_Int) &&
  i >= (Rust_primitives.Hax.Int.from_machine Core.Num.impl_i32__MIN <: Hax_lib.Int.t_Int)

let add_pre (lhs rhs: t_Array i32 (mk_usize 8)) =
  Hax_lib.v_forall #usize
    (fun i ->
        let i:usize = i in
        Hax_lib.implies (i <. v_COEFFICIENTS_IN_SIMD_UNIT <: bool)
          (fun temp_0_ ->
              let _:Prims.unit = temp_0_ in
              int_is_i32 ((Rust_primitives.Hax.Int.from_machine (lhs.[ i ] <: i32)
                    <:
                    Hax_lib.Int.t_Int) +
                  (Rust_primitives.Hax.Int.from_machine (rhs.[ i ] <: i32) <: Hax_lib.Int.t_Int)
                  <:
                  Hax_lib.Int.t_Int)
              <:
              bool)
        <:
        bool)

let add_post (lhs rhs future_lhs: t_Array i32 (mk_usize 8)) =
  Hax_lib.v_forall #usize
    (fun i ->
        let i:usize = i in
        Hax_lib.implies (i <. v_COEFFICIENTS_IN_SIMD_UNIT <: bool)
          (fun temp_0_ ->
              let _:Prims.unit = temp_0_ in
              (Rust_primitives.Hax.Int.from_machine (future_lhs.[ i ] <: i32) <: Hax_lib.Int.t_Int) =
              ((Rust_primitives.Hax.Int.from_machine (lhs.[ i ] <: i32) <: Hax_lib.Int.t_Int) +
                (Rust_primitives.Hax.Int.from_machine (rhs.[ i ] <: i32) <: Hax_lib.Int.t_Int)
                <:
                Hax_lib.Int.t_Int)
              <:
              bool)
        <:
        bool)

let sub_pre (lhs rhs: t_Array i32 (mk_usize 8)) =
  Hax_lib.v_forall #usize
    (fun i ->
        let i:usize = i in
        Hax_lib.implies (i <. v_COEFFICIENTS_IN_SIMD_UNIT <: bool)
          (fun temp_0_ ->
              let _:Prims.unit = temp_0_ in
              int_is_i32 ((Rust_primitives.Hax.Int.from_machine (lhs.[ i ] <: i32)
                    <:
                    Hax_lib.Int.t_Int) -
                  (Rust_primitives.Hax.Int.from_machine (rhs.[ i ] <: i32) <: Hax_lib.Int.t_Int)
                  <:
                  Hax_lib.Int.t_Int)
              <:
              bool)
        <:
        bool)

let sub_post (lhs rhs future_lhs: t_Array i32 (mk_usize 8)) =
  Hax_lib.v_forall #usize
    (fun i ->
        let i:usize = i in
        Hax_lib.implies (i <. v_COEFFICIENTS_IN_SIMD_UNIT <: bool)
          (fun temp_0_ ->
              let _:Prims.unit = temp_0_ in
              (Rust_primitives.Hax.Int.from_machine (future_lhs.[ i ] <: i32) <: Hax_lib.Int.t_Int) =
              ((Rust_primitives.Hax.Int.from_machine (lhs.[ i ] <: i32) <: Hax_lib.Int.t_Int) -
                (Rust_primitives.Hax.Int.from_machine (rhs.[ i ] <: i32) <: Hax_lib.Int.t_Int)
                <:
                Hax_lib.Int.t_Int)
              <:
              bool)
        <:
        bool)
