module Libcrux_sha3.Generic_keccak
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_sha3.Traits in
  let open Libcrux_sha3.Traits.Internal in
  ()

let v_ROUNDCONSTANTS: t_Array u64 (sz 24) =
  let list =
    [
      1uL; 32898uL; 9223372036854808714uL; 9223372039002292224uL; 32907uL; 2147483649uL;
      9223372039002292353uL; 9223372036854808585uL; 138uL; 136uL; 2147516425uL; 2147483658uL;
      2147516555uL; 9223372036854775947uL; 9223372036854808713uL; 9223372036854808579uL;
      9223372036854808578uL; 9223372036854775936uL; 32778uL; 9223372039002259466uL;
      9223372039002292353uL; 9223372036854808704uL; 2147483649uL; 9223372039002292232uL
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 24);
  Rust_primitives.Hax.array_of_list 24 list

let v__PI: t_Array usize (sz 24) =
  let list =
    [
      sz 6; sz 12; sz 18; sz 24; sz 3; sz 9; sz 10; sz 16; sz 22; sz 1; sz 7; sz 13; sz 19; sz 20;
      sz 4; sz 5; sz 11; sz 17; sz 23; sz 2; sz 8; sz 14; sz 15; sz 21
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 24);
  Rust_primitives.Hax.array_of_list 24 list

/// From here, everything is generic
let v__ROTC: t_Array usize (sz 24) =
  let list =
    [
      sz 1; sz 62; sz 28; sz 27; sz 36; sz 44; sz 6; sz 55; sz 20; sz 3; sz 10; sz 43; sz 25; sz 39;
      sz 41; sz 45; sz 15; sz 21; sz 8; sz 18; sz 2; sz 61; sz 56; sz 14
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 24);
  Rust_primitives.Hax.array_of_list 24 list

(* item error backend: ((Diagnostics.Context.Backend FStar),
 Types.AttributeRejected {
   reason =
   "a type cannot be opaque if its module is not extracted as an interface"})

Last AST:
#[_hax::json("\"OpaqueType\"")]
#[no_std()]
#[forbid(unsafe_code)]
#[feature(register_tool)]
#[register_tool(_hax)]
struct t_KeccakState<const N: int, T>
where
    _: libcrux_sha3::traits::t_KeccakStateItem<T, generic_value!(todo)>,
{
    f_st: [[T; 5]; 5],
}
 *)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (v_N: usize)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N)
    : Core.Ops.Index.t_Index (t_KeccakState v_N v_T) usize =
  {
    f_Output = t_Array v_T (sz 5);
    f_index_pre = (fun (self: t_KeccakState v_N v_T) (index: usize) -> true);
    f_index_post
    =
    (fun (self: t_KeccakState v_N v_T) (index: usize) (out: t_Array v_T (sz 5)) -> true);
    f_index = fun (self: t_KeccakState v_N v_T) (index: usize) -> self.f_st.[ index ]
  }

/// Create a new Shake128 x4 state.
let impl_1__new
      (v_N: usize)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N)
      (_: Prims.unit)
    : t_KeccakState v_N v_T =
  {
    f_st
    =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat (Libcrux_sha3.Traits.Internal.f_zero #v_T
              v_N
              ()
            <:
            v_T)
          (sz 5)
        <:
        t_Array v_T (sz 5))
      (sz 5)
  }
  <:
  t_KeccakState v_N v_T

let chi
      (v_N: usize)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N)
      (s: t_KeccakState v_N v_T)
    : t_KeccakState v_N v_T =
  let old:t_Array (t_Array v_T (sz 5)) (sz 5) = s.f_st in
  let s, hax_temp_output:t_KeccakState v_N v_T =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 5 }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      s
      (fun s i ->
          let s:t_KeccakState v_N v_T = s in
          let i:usize = i in
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
                  usize)
                ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 5 }
                  <:
                  Core.Ops.Range.t_Range usize)
              <:
              Core.Ops.Range.t_Range usize)
            s
            (fun s j ->
                let s:t_KeccakState v_N v_T = s in
                let j:usize = j in
                {
                  s with
                  f_st
                  =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
                    i
                    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ i ]
                          <:
                          t_Array v_T (sz 5))
                        j
                        (Libcrux_sha3.Traits.Internal.f_and_not_xor #v_T
                            v_N
                            ((s.f_st.[ i ] <: t_Array v_T (sz 5)).[ j ] <: v_T)
                            ((old.[ i ] <: t_Array v_T (sz 5)).[ (j +! sz 2 <: usize) %! sz 5
                                <:
                                usize ]
                              <:
                              v_T)
                            ((old.[ i ] <: t_Array v_T (sz 5)).[ (j +! sz 1 <: usize) %! sz 5
                                <:
                                usize ]
                              <:
                              v_T)
                          <:
                          v_T)
                      <:
                      t_Array v_T (sz 5))
                  <:
                  t_Array (t_Array v_T (sz 5)) (sz 5)
                }
                <:
                t_KeccakState v_N v_T)
          <:
          t_KeccakState v_N v_T)
  in
  s

let iota
      (v_N: usize)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N)
      (s: t_KeccakState v_N v_T)
      (i: usize)
    : t_KeccakState v_N v_T =
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 0)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 0 ]
              <:
              t_Array v_T (sz 5))
            (sz 0)
            (Libcrux_sha3.Traits.Internal.f_xor_constant #v_T
                v_N
                ((s.f_st.[ sz 0 ] <: t_Array v_T (sz 5)).[ sz 0 ] <: v_T)
                (v_ROUNDCONSTANTS.[ i ] <: u64)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  s

let pi
      (v_N: usize)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N)
      (s: t_KeccakState v_N v_T)
    : t_KeccakState v_N v_T =
  let old:t_Array (t_Array v_T (sz 5)) (sz 5) =
    Core.Clone.f_clone #(t_Array (t_Array v_T (sz 5)) (sz 5)) s.f_st
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 0)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 0 ]
              <:
              t_Array v_T (sz 5))
            (sz 1)
            ((old.[ sz 1 ] <: t_Array v_T (sz 5)).[ sz 1 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 0)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 0 ]
              <:
              t_Array v_T (sz 5))
            (sz 2)
            ((old.[ sz 2 ] <: t_Array v_T (sz 5)).[ sz 2 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 0)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 0 ]
              <:
              t_Array v_T (sz 5))
            (sz 3)
            ((old.[ sz 3 ] <: t_Array v_T (sz 5)).[ sz 3 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 0)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 0 ]
              <:
              t_Array v_T (sz 5))
            (sz 4)
            ((old.[ sz 4 ] <: t_Array v_T (sz 5)).[ sz 4 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 1)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 1 ]
              <:
              t_Array v_T (sz 5))
            (sz 0)
            ((old.[ sz 0 ] <: t_Array v_T (sz 5)).[ sz 3 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 1)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 1 ]
              <:
              t_Array v_T (sz 5))
            (sz 1)
            ((old.[ sz 1 ] <: t_Array v_T (sz 5)).[ sz 4 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 1)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 1 ]
              <:
              t_Array v_T (sz 5))
            (sz 2)
            ((old.[ sz 2 ] <: t_Array v_T (sz 5)).[ sz 0 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 1)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 1 ]
              <:
              t_Array v_T (sz 5))
            (sz 3)
            ((old.[ sz 3 ] <: t_Array v_T (sz 5)).[ sz 1 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 1)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 1 ]
              <:
              t_Array v_T (sz 5))
            (sz 4)
            ((old.[ sz 4 ] <: t_Array v_T (sz 5)).[ sz 2 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 2)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 2 ]
              <:
              t_Array v_T (sz 5))
            (sz 0)
            ((old.[ sz 0 ] <: t_Array v_T (sz 5)).[ sz 1 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 2)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 2 ]
              <:
              t_Array v_T (sz 5))
            (sz 1)
            ((old.[ sz 1 ] <: t_Array v_T (sz 5)).[ sz 2 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 2)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 2 ]
              <:
              t_Array v_T (sz 5))
            (sz 2)
            ((old.[ sz 2 ] <: t_Array v_T (sz 5)).[ sz 3 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 2)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 2 ]
              <:
              t_Array v_T (sz 5))
            (sz 3)
            ((old.[ sz 3 ] <: t_Array v_T (sz 5)).[ sz 4 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 2)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 2 ]
              <:
              t_Array v_T (sz 5))
            (sz 4)
            ((old.[ sz 4 ] <: t_Array v_T (sz 5)).[ sz 0 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 3)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 3 ]
              <:
              t_Array v_T (sz 5))
            (sz 0)
            ((old.[ sz 0 ] <: t_Array v_T (sz 5)).[ sz 4 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 3)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 3 ]
              <:
              t_Array v_T (sz 5))
            (sz 1)
            ((old.[ sz 1 ] <: t_Array v_T (sz 5)).[ sz 0 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 3)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 3 ]
              <:
              t_Array v_T (sz 5))
            (sz 2)
            ((old.[ sz 2 ] <: t_Array v_T (sz 5)).[ sz 1 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 3)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 3 ]
              <:
              t_Array v_T (sz 5))
            (sz 3)
            ((old.[ sz 3 ] <: t_Array v_T (sz 5)).[ sz 2 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 3)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 3 ]
              <:
              t_Array v_T (sz 5))
            (sz 4)
            ((old.[ sz 4 ] <: t_Array v_T (sz 5)).[ sz 3 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 4)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 4 ]
              <:
              t_Array v_T (sz 5))
            (sz 0)
            ((old.[ sz 0 ] <: t_Array v_T (sz 5)).[ sz 2 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 4)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 4 ]
              <:
              t_Array v_T (sz 5))
            (sz 1)
            ((old.[ sz 1 ] <: t_Array v_T (sz 5)).[ sz 3 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 4)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 4 ]
              <:
              t_Array v_T (sz 5))
            (sz 2)
            ((old.[ sz 2 ] <: t_Array v_T (sz 5)).[ sz 4 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 4)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 4 ]
              <:
              t_Array v_T (sz 5))
            (sz 3)
            ((old.[ sz 3 ] <: t_Array v_T (sz 5)).[ sz 0 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 4)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 4 ]
              <:
              t_Array v_T (sz 5))
            (sz 4)
            ((old.[ sz 4 ] <: t_Array v_T (sz 5)).[ sz 1 ] <: v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  s

let squeeze_first_and_last
      (v_N: usize)
      (#v_T: Type0)
      (v_RATE v_SIZE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N)
      (s: t_KeccakState v_N v_T)
      (out: t_Array (t_Array u8 v_SIZE) v_N)
    : t_Array (t_Array u8 v_SIZE) v_N =
  let b:t_Array (t_Array u8 (sz 200)) v_N =
    Libcrux_sha3.Traits.Internal.f_store_block_full #v_T v_N v_RATE s.f_st
  in
  let out, hax_temp_output:t_Array (t_Array u8 v_SIZE) v_N =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_N }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      out
      (fun out i ->
          let out:t_Array (t_Array u8 v_SIZE) v_N = out in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
            i
            (Core.Slice.impl__copy_from_slice #u8
                (out.[ i ] <: t_Array u8 v_SIZE)
                ((b.[ i ] <: t_Array u8 (sz 200)).[ {
                      Core.Ops.Range.f_start = sz 0;
                      Core.Ops.Range.f_end = v_SIZE
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              t_Array u8 v_SIZE)
          <:
          t_Array (t_Array u8 v_SIZE) v_N)
  in
  out

let squeeze_first_block
      (v_N: usize)
      (#v_T: Type0)
      (v_RATE v_SIZE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N)
      (s: t_KeccakState v_N v_T)
      (out: t_Array (t_Array u8 v_SIZE) v_N)
    : t_Array (t_Array u8 v_SIZE) v_N =
  let hax_temp_output, out:(Prims.unit & t_Array (t_Array u8 v_SIZE) v_N) =
    (), Libcrux_sha3.Traits.Internal.f_store_block #v_T v_N v_RATE v_SIZE s.f_st out (sz 0)
    <:
    (Prims.unit & t_Array (t_Array u8 v_SIZE) v_N)
  in
  out

let theta_rho
      (v_N: usize)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N)
      (s: t_KeccakState v_N v_T)
    : t_KeccakState v_N v_T =
  let (c: t_Array v_T (sz 5)):t_Array v_T (sz 5) =
    let list =
      [
        Libcrux_sha3.Traits.Internal.f_xor5 #v_T
          v_N
          ((s.f_st.[ sz 0 ] <: t_Array v_T (sz 5)).[ sz 0 ] <: v_T)
          ((s.f_st.[ sz 1 ] <: t_Array v_T (sz 5)).[ sz 0 ] <: v_T)
          ((s.f_st.[ sz 2 ] <: t_Array v_T (sz 5)).[ sz 0 ] <: v_T)
          ((s.f_st.[ sz 3 ] <: t_Array v_T (sz 5)).[ sz 0 ] <: v_T)
          ((s.f_st.[ sz 4 ] <: t_Array v_T (sz 5)).[ sz 0 ] <: v_T);
        Libcrux_sha3.Traits.Internal.f_xor5 #v_T
          v_N
          ((s.f_st.[ sz 0 ] <: t_Array v_T (sz 5)).[ sz 1 ] <: v_T)
          ((s.f_st.[ sz 1 ] <: t_Array v_T (sz 5)).[ sz 1 ] <: v_T)
          ((s.f_st.[ sz 2 ] <: t_Array v_T (sz 5)).[ sz 1 ] <: v_T)
          ((s.f_st.[ sz 3 ] <: t_Array v_T (sz 5)).[ sz 1 ] <: v_T)
          ((s.f_st.[ sz 4 ] <: t_Array v_T (sz 5)).[ sz 1 ] <: v_T);
        Libcrux_sha3.Traits.Internal.f_xor5 #v_T
          v_N
          ((s.f_st.[ sz 0 ] <: t_Array v_T (sz 5)).[ sz 2 ] <: v_T)
          ((s.f_st.[ sz 1 ] <: t_Array v_T (sz 5)).[ sz 2 ] <: v_T)
          ((s.f_st.[ sz 2 ] <: t_Array v_T (sz 5)).[ sz 2 ] <: v_T)
          ((s.f_st.[ sz 3 ] <: t_Array v_T (sz 5)).[ sz 2 ] <: v_T)
          ((s.f_st.[ sz 4 ] <: t_Array v_T (sz 5)).[ sz 2 ] <: v_T);
        Libcrux_sha3.Traits.Internal.f_xor5 #v_T
          v_N
          ((s.f_st.[ sz 0 ] <: t_Array v_T (sz 5)).[ sz 3 ] <: v_T)
          ((s.f_st.[ sz 1 ] <: t_Array v_T (sz 5)).[ sz 3 ] <: v_T)
          ((s.f_st.[ sz 2 ] <: t_Array v_T (sz 5)).[ sz 3 ] <: v_T)
          ((s.f_st.[ sz 3 ] <: t_Array v_T (sz 5)).[ sz 3 ] <: v_T)
          ((s.f_st.[ sz 4 ] <: t_Array v_T (sz 5)).[ sz 3 ] <: v_T);
        Libcrux_sha3.Traits.Internal.f_xor5 #v_T
          v_N
          ((s.f_st.[ sz 0 ] <: t_Array v_T (sz 5)).[ sz 4 ] <: v_T)
          ((s.f_st.[ sz 1 ] <: t_Array v_T (sz 5)).[ sz 4 ] <: v_T)
          ((s.f_st.[ sz 2 ] <: t_Array v_T (sz 5)).[ sz 4 ] <: v_T)
          ((s.f_st.[ sz 3 ] <: t_Array v_T (sz 5)).[ sz 4 ] <: v_T)
          ((s.f_st.[ sz 4 ] <: t_Array v_T (sz 5)).[ sz 4 ] <: v_T)
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list
  in
  let (t: t_Array v_T (sz 5)):t_Array v_T (sz 5) =
    let list =
      [
        Libcrux_sha3.Traits.Internal.f_rotate_left1_and_xor #v_T
          v_N
          (c.[ (sz 0 +! sz 4 <: usize) %! sz 5 <: usize ] <: v_T)
          (c.[ (sz 0 +! sz 1 <: usize) %! sz 5 <: usize ] <: v_T);
        Libcrux_sha3.Traits.Internal.f_rotate_left1_and_xor #v_T
          v_N
          (c.[ (sz 1 +! sz 4 <: usize) %! sz 5 <: usize ] <: v_T)
          (c.[ (sz 1 +! sz 1 <: usize) %! sz 5 <: usize ] <: v_T);
        Libcrux_sha3.Traits.Internal.f_rotate_left1_and_xor #v_T
          v_N
          (c.[ (sz 2 +! sz 4 <: usize) %! sz 5 <: usize ] <: v_T)
          (c.[ (sz 2 +! sz 1 <: usize) %! sz 5 <: usize ] <: v_T);
        Libcrux_sha3.Traits.Internal.f_rotate_left1_and_xor #v_T
          v_N
          (c.[ (sz 3 +! sz 4 <: usize) %! sz 5 <: usize ] <: v_T)
          (c.[ (sz 3 +! sz 1 <: usize) %! sz 5 <: usize ] <: v_T);
        Libcrux_sha3.Traits.Internal.f_rotate_left1_and_xor #v_T
          v_N
          (c.[ (sz 4 +! sz 4 <: usize) %! sz 5 <: usize ] <: v_T)
          (c.[ (sz 4 +! sz 1 <: usize) %! sz 5 <: usize ] <: v_T)
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
    Rust_primitives.Hax.array_of_list 5 list
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 0)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 0 ]
              <:
              t_Array v_T (sz 5))
            (sz 0)
            (Libcrux_sha3.Traits.Internal.f_xor #v_T
                v_N
                ((s.f_st.[ sz 0 ] <: t_Array v_T (sz 5)).[ sz 0 ] <: v_T)
                (t.[ sz 0 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 1)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 1 ]
              <:
              t_Array v_T (sz 5))
            (sz 0)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                36l
                28l
                ((s.f_st.[ sz 1 ] <: t_Array v_T (sz 5)).[ sz 0 ] <: v_T)
                (t.[ sz 0 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 2)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 2 ]
              <:
              t_Array v_T (sz 5))
            (sz 0)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                3l
                61l
                ((s.f_st.[ sz 2 ] <: t_Array v_T (sz 5)).[ sz 0 ] <: v_T)
                (t.[ sz 0 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 3)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 3 ]
              <:
              t_Array v_T (sz 5))
            (sz 0)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                41l
                23l
                ((s.f_st.[ sz 3 ] <: t_Array v_T (sz 5)).[ sz 0 ] <: v_T)
                (t.[ sz 0 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 4)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 4 ]
              <:
              t_Array v_T (sz 5))
            (sz 0)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                18l
                46l
                ((s.f_st.[ sz 4 ] <: t_Array v_T (sz 5)).[ sz 0 ] <: v_T)
                (t.[ sz 0 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 0)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 0 ]
              <:
              t_Array v_T (sz 5))
            (sz 1)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                1l
                63l
                ((s.f_st.[ sz 0 ] <: t_Array v_T (sz 5)).[ sz 1 ] <: v_T)
                (t.[ sz 1 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 1)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 1 ]
              <:
              t_Array v_T (sz 5))
            (sz 1)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                44l
                20l
                ((s.f_st.[ sz 1 ] <: t_Array v_T (sz 5)).[ sz 1 ] <: v_T)
                (t.[ sz 1 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 2)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 2 ]
              <:
              t_Array v_T (sz 5))
            (sz 1)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                10l
                54l
                ((s.f_st.[ sz 2 ] <: t_Array v_T (sz 5)).[ sz 1 ] <: v_T)
                (t.[ sz 1 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 3)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 3 ]
              <:
              t_Array v_T (sz 5))
            (sz 1)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                45l
                19l
                ((s.f_st.[ sz 3 ] <: t_Array v_T (sz 5)).[ sz 1 ] <: v_T)
                (t.[ sz 1 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 4)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 4 ]
              <:
              t_Array v_T (sz 5))
            (sz 1)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                2l
                62l
                ((s.f_st.[ sz 4 ] <: t_Array v_T (sz 5)).[ sz 1 ] <: v_T)
                (t.[ sz 1 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 0)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 0 ]
              <:
              t_Array v_T (sz 5))
            (sz 2)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                62l
                2l
                ((s.f_st.[ sz 0 ] <: t_Array v_T (sz 5)).[ sz 2 ] <: v_T)
                (t.[ sz 2 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 1)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 1 ]
              <:
              t_Array v_T (sz 5))
            (sz 2)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                6l
                58l
                ((s.f_st.[ sz 1 ] <: t_Array v_T (sz 5)).[ sz 2 ] <: v_T)
                (t.[ sz 2 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 2)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 2 ]
              <:
              t_Array v_T (sz 5))
            (sz 2)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                43l
                21l
                ((s.f_st.[ sz 2 ] <: t_Array v_T (sz 5)).[ sz 2 ] <: v_T)
                (t.[ sz 2 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 3)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 3 ]
              <:
              t_Array v_T (sz 5))
            (sz 2)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                15l
                49l
                ((s.f_st.[ sz 3 ] <: t_Array v_T (sz 5)).[ sz 2 ] <: v_T)
                (t.[ sz 2 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 4)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 4 ]
              <:
              t_Array v_T (sz 5))
            (sz 2)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                61l
                3l
                ((s.f_st.[ sz 4 ] <: t_Array v_T (sz 5)).[ sz 2 ] <: v_T)
                (t.[ sz 2 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 0)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 0 ]
              <:
              t_Array v_T (sz 5))
            (sz 3)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                28l
                36l
                ((s.f_st.[ sz 0 ] <: t_Array v_T (sz 5)).[ sz 3 ] <: v_T)
                (t.[ sz 3 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 1)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 1 ]
              <:
              t_Array v_T (sz 5))
            (sz 3)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                55l
                9l
                ((s.f_st.[ sz 1 ] <: t_Array v_T (sz 5)).[ sz 3 ] <: v_T)
                (t.[ sz 3 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 2)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 2 ]
              <:
              t_Array v_T (sz 5))
            (sz 3)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                25l
                39l
                ((s.f_st.[ sz 2 ] <: t_Array v_T (sz 5)).[ sz 3 ] <: v_T)
                (t.[ sz 3 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 3)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 3 ]
              <:
              t_Array v_T (sz 5))
            (sz 3)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                21l
                43l
                ((s.f_st.[ sz 3 ] <: t_Array v_T (sz 5)).[ sz 3 ] <: v_T)
                (t.[ sz 3 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 4)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 4 ]
              <:
              t_Array v_T (sz 5))
            (sz 3)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                56l
                8l
                ((s.f_st.[ sz 4 ] <: t_Array v_T (sz 5)).[ sz 3 ] <: v_T)
                (t.[ sz 3 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 0)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 0 ]
              <:
              t_Array v_T (sz 5))
            (sz 4)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                27l
                37l
                ((s.f_st.[ sz 0 ] <: t_Array v_T (sz 5)).[ sz 4 ] <: v_T)
                (t.[ sz 4 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 1)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 1 ]
              <:
              t_Array v_T (sz 5))
            (sz 4)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                20l
                44l
                ((s.f_st.[ sz 1 ] <: t_Array v_T (sz 5)).[ sz 4 ] <: v_T)
                (t.[ sz 4 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 2)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 2 ]
              <:
              t_Array v_T (sz 5))
            (sz 4)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                39l
                25l
                ((s.f_st.[ sz 2 ] <: t_Array v_T (sz 5)).[ sz 4 ] <: v_T)
                (t.[ sz 4 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 3)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 3 ]
              <:
              t_Array v_T (sz 5))
            (sz 4)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                8l
                56l
                ((s.f_st.[ sz 3 ] <: t_Array v_T (sz 5)).[ sz 4 ] <: v_T)
                (t.[ sz 4 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  let s:t_KeccakState v_N v_T =
    {
      s with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.f_st
        (sz 4)
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.f_st.[ sz 4 ]
              <:
              t_Array v_T (sz 5))
            (sz 4)
            (Libcrux_sha3.Traits.Internal.f_xor_and_rotate #v_T
                v_N
                14l
                50l
                ((s.f_st.[ sz 4 ] <: t_Array v_T (sz 5)).[ sz 4 ] <: v_T)
                (t.[ sz 4 ] <: v_T)
              <:
              v_T)
          <:
          t_Array v_T (sz 5))
    }
    <:
    t_KeccakState v_N v_T
  in
  s

let keccakf1600
      (v_N: usize)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N)
      (s: t_KeccakState v_N v_T)
    : t_KeccakState v_N v_T =
  let s, hax_temp_output:t_KeccakState v_N v_T =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 24 }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      s
      (fun s i ->
          let s:t_KeccakState v_N v_T = s in
          let i:usize = i in
          let s:t_KeccakState v_N v_T = theta_rho v_N #v_T s in
          let s:t_KeccakState v_N v_T = pi v_N #v_T s in
          let s:t_KeccakState v_N v_T = chi v_N #v_T s in
          let s:t_KeccakState v_N v_T = iota v_N #v_T s i in
          s)
  in
  s

let absorb_block
      (v_N: usize)
      (#v_T: Type0)
      (v_RATE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N)
      (s: t_KeccakState v_N v_T)
      (blocks: t_Array (t_Slice u8) v_N)
    : t_KeccakState v_N v_T =
  let s:t_KeccakState v_N v_T =
    { s with f_st = Libcrux_sha3.Traits.Internal.f_load_block #v_T v_N v_RATE s.f_st blocks }
    <:
    t_KeccakState v_N v_T
  in
  let hax_temp_output, s:(Prims.unit & t_KeccakState v_N v_T) =
    (), keccakf1600 v_N #v_T s <: (Prims.unit & t_KeccakState v_N v_T)
  in
  s

let absorb_final
      (v_N: usize)
      (#v_T: Type0)
      (v_RATE: usize)
      (v_DELIM: u8)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N)
      (s: t_KeccakState v_N v_T)
      (last: t_Array (t_Slice u8) v_N)
    : t_KeccakState v_N v_T =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.((v_N >. sz 0 <: bool) &&
            ((Core.Slice.impl__len #u8 (last.[ sz 0 ] <: t_Slice u8) <: usize) <. v_RATE <: bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: N > 0 && last[0].len() < RATE"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let last_len:usize = Core.Slice.impl__len #u8 (last.[ sz 0 ] <: t_Slice u8) in
  let blocks:t_Array (t_Array u8 (sz 200)) v_N =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 200) <: t_Array u8 (sz 200)) v_N
  in
  let blocks:t_Array (t_Array u8 (sz 200)) v_N =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_N }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      blocks
      (fun blocks i ->
          let blocks:t_Array (t_Array u8 (sz 200)) v_N = blocks in
          let i:usize = i in
          let blocks:t_Array (t_Array u8 (sz 200)) v_N =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize blocks
              i
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (blocks.[ i ]
                    <:
                    t_Array u8 (sz 200))
                  ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = last_len }
                    <:
                    Core.Ops.Range.t_Range usize)
                  (Core.Slice.impl__copy_from_slice #u8
                      ((blocks.[ i ] <: t_Array u8 (sz 200)).[ {
                            Core.Ops.Range.f_start = sz 0;
                            Core.Ops.Range.f_end = last_len
                          }
                          <:
                          Core.Ops.Range.t_Range usize ]
                        <:
                        t_Slice u8)
                      (last.[ i ] <: t_Slice u8)
                    <:
                    t_Slice u8)
                <:
                t_Array u8 (sz 200))
          in
          let blocks:t_Array (t_Array u8 (sz 200)) v_N =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize blocks
              i
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (blocks.[ i ]
                    <:
                    t_Array u8 (sz 200))
                  last_len
                  v_DELIM
                <:
                t_Array u8 (sz 200))
          in
          let blocks:t_Array (t_Array u8 (sz 200)) v_N =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize blocks
              i
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (blocks.[ i ]
                    <:
                    t_Array u8 (sz 200))
                  (v_RATE -! sz 1 <: usize)
                  (((blocks.[ i ] <: t_Array u8 (sz 200)).[ v_RATE -! sz 1 <: usize ] <: u8) |.
                    128uy
                    <:
                    u8)
                <:
                t_Array u8 (sz 200))
          in
          blocks)
  in
  let s:t_KeccakState v_N v_T =
    { s with f_st = Libcrux_sha3.Traits.Internal.f_load_block_full #v_T v_N v_RATE s.f_st blocks }
    <:
    t_KeccakState v_N v_T
  in
  let hax_temp_output, s:(Prims.unit & t_KeccakState v_N v_T) =
    (), keccakf1600 v_N #v_T s <: (Prims.unit & t_KeccakState v_N v_T)
  in
  s

let squeeze_last
      (v_N: usize)
      (#v_T: Type0)
      (v_RATE v_SIZE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N)
      (s: t_KeccakState v_N v_T)
      (out: t_Array (t_Array u8 v_SIZE) v_N)
      (start: usize)
    : t_Array (t_Array u8 v_SIZE) v_N =
  let s:t_KeccakState v_N v_T = keccakf1600 v_N #v_T s in
  let b:t_Array (t_Array u8 (sz 200)) v_N =
    Libcrux_sha3.Traits.Internal.f_store_block_full #v_T v_N v_RATE s.f_st
  in
  let out, hax_temp_output:t_Array (t_Array u8 v_SIZE) v_N =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_N }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      out
      (fun out i ->
          let out:t_Array (t_Array u8 v_SIZE) v_N = out in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
            i
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (out.[ i ]
                  <:
                  t_Array u8 v_SIZE)
                ({ Core.Ops.Range.f_start = start; Core.Ops.Range.f_end = v_SIZE }
                  <:
                  Core.Ops.Range.t_Range usize)
                (Core.Slice.impl__copy_from_slice #u8
                    ((out.[ i ] <: t_Array u8 v_SIZE).[ {
                          Core.Ops.Range.f_start = start;
                          Core.Ops.Range.f_end = v_SIZE
                        }
                        <:
                        Core.Ops.Range.t_Range usize ]
                      <:
                      t_Slice u8)
                    ((b.[ i ] <: t_Array u8 (sz 200)).[ {
                          Core.Ops.Range.f_start = sz 0;
                          Core.Ops.Range.f_end = v_SIZE -! start <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize ]
                      <:
                      t_Slice u8)
                  <:
                  t_Slice u8)
              <:
              t_Array u8 v_SIZE)
          <:
          t_Array (t_Array u8 v_SIZE) v_N)
  in
  out

let squeeze_next_block
      (v_N: usize)
      (#v_T: Type0)
      (v_RATE v_SIZE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N)
      (s: t_KeccakState v_N v_T)
      (out: t_Array (t_Array u8 v_SIZE) v_N)
      (start: usize)
    : (t_KeccakState v_N v_T & t_Array (t_Array u8 v_SIZE) v_N) =
  let s:t_KeccakState v_N v_T = keccakf1600 v_N #v_T s in
  let hax_temp_output, out:(Prims.unit & t_Array (t_Array u8 v_SIZE) v_N) =
    (), Libcrux_sha3.Traits.Internal.f_store_block #v_T v_N v_RATE v_SIZE s.f_st out start
    <:
    (Prims.unit & t_Array (t_Array u8 v_SIZE) v_N)
  in
  s, out <: (t_KeccakState v_N v_T & t_Array (t_Array u8 v_SIZE) v_N)

let keccak
      (v_N: usize)
      (#v_T: Type0)
      (v_RATE v_SIZE: usize)
      (v_DELIM: u8)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N)
      (data: t_Array (t_Slice u8) v_N)
      (out: t_Array (t_Array u8 v_SIZE) v_N)
    : t_Array (t_Array u8 v_SIZE) v_N =
  let s:t_KeccakState v_N v_T = impl_1__new v_N #v_T () in
  let s:t_KeccakState v_N v_T =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end
              =
              (Core.Slice.impl__len #u8 (data.[ sz 0 ] <: t_Slice u8) <: usize) /! v_RATE <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      s
      (fun s i ->
          let s:t_KeccakState v_N v_T = s in
          let i:usize = i in
          absorb_block v_N
            #v_T
            v_RATE
            s
            (Libcrux_sha3.Traits.Internal.f_slice_n #v_T v_N data (i *! v_RATE <: usize) v_RATE
              <:
              t_Array (t_Slice u8) v_N)
          <:
          t_KeccakState v_N v_T)
  in
  let rem:usize = (Core.Slice.impl__len #u8 (data.[ sz 0 ] <: t_Slice u8) <: usize) %! v_RATE in
  let s:t_KeccakState v_N v_T =
    absorb_final v_N
      #v_T
      v_RATE
      v_DELIM
      s
      (Libcrux_sha3.Traits.Internal.f_slice_n #v_T
          v_N
          data
          ((Core.Slice.impl__len #u8 (data.[ sz 0 ] <: t_Slice u8) <: usize) -! rem <: usize)
          rem
        <:
        t_Array (t_Slice u8) v_N)
  in
  let outlen:usize =
    Core.Slice.impl__len #u8
      (Rust_primitives.unsize (out.[ sz 0 ] <: t_Array u8 v_SIZE) <: t_Slice u8)
  in
  let blocks:usize = outlen /! v_RATE in
  let last:usize = outlen -! (outlen %! v_RATE <: usize) in
  let (out, s), hax_temp_output:((t_Array (t_Array u8 v_SIZE) v_N & t_KeccakState v_N v_T) &
    Prims.unit) =
    if blocks =. sz 0
    then
      (squeeze_first_and_last v_N #v_T v_RATE v_SIZE s out, s
        <:
        (t_Array (t_Array u8 v_SIZE) v_N & t_KeccakState v_N v_T)),
      ()
      <:
      ((t_Array (t_Array u8 v_SIZE) v_N & t_KeccakState v_N v_T) & Prims.unit)
    else
      let out:t_Array (t_Array u8 v_SIZE) v_N = squeeze_first_block v_N #v_T v_RATE v_SIZE s out in
      let out, s:(t_Array (t_Array u8 v_SIZE) v_N & t_KeccakState v_N v_T) =
        Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
                usize)
              ({ Core.Ops.Range.f_start = sz 1; Core.Ops.Range.f_end = blocks }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Core.Ops.Range.t_Range usize)
          (out, s <: (t_Array (t_Array u8 v_SIZE) v_N & t_KeccakState v_N v_T))
          (fun temp_0_ i ->
              let out, s:(t_Array (t_Array u8 v_SIZE) v_N & t_KeccakState v_N v_T) = temp_0_ in
              let i:usize = i in
              let tmp0, tmp1:(t_KeccakState v_N v_T & t_Array (t_Array u8 v_SIZE) v_N) =
                squeeze_next_block v_N #v_T v_RATE v_SIZE s out (i *! v_RATE <: usize)
              in
              let s:t_KeccakState v_N v_T = tmp0 in
              let out:t_Array (t_Array u8 v_SIZE) v_N = tmp1 in
              out, s <: (t_Array (t_Array u8 v_SIZE) v_N & t_KeccakState v_N v_T))
      in
      if last <. outlen
      then
        (squeeze_last v_N #v_T v_RATE v_SIZE s out (blocks *! v_RATE <: usize), s
          <:
          (t_Array (t_Array u8 v_SIZE) v_N & t_KeccakState v_N v_T)),
        ()
        <:
        ((t_Array (t_Array u8 v_SIZE) v_N & t_KeccakState v_N v_T) & Prims.unit)
      else
        (out, s <: (t_Array (t_Array u8 v_SIZE) v_N & t_KeccakState v_N v_T)), ()
        <:
        ((t_Array (t_Array u8 v_SIZE) v_N & t_KeccakState v_N v_T) & Prims.unit)
  in
  out

let squeeze_first_five_blocks
      (v_N: usize)
      (#v_T: Type0)
      (v_RATE v_SIZE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N)
      (s: t_KeccakState v_N v_T)
      (out: t_Array (t_Array u8 v_SIZE) v_N)
    : (t_KeccakState v_N v_T & t_Array (t_Array u8 v_SIZE) v_N) =
  let out:t_Array (t_Array u8 v_SIZE) v_N = squeeze_first_block v_N #v_T v_RATE v_SIZE s out in
  let tmp0, tmp1:(t_KeccakState v_N v_T & t_Array (t_Array u8 v_SIZE) v_N) =
    squeeze_next_block v_N #v_T v_RATE v_SIZE s out v_RATE
  in
  let s:t_KeccakState v_N v_T = tmp0 in
  let out:t_Array (t_Array u8 v_SIZE) v_N = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(t_KeccakState v_N v_T & t_Array (t_Array u8 v_SIZE) v_N) =
    squeeze_next_block v_N #v_T v_RATE v_SIZE s out (sz 2 *! v_RATE <: usize)
  in
  let s:t_KeccakState v_N v_T = tmp0 in
  let out:t_Array (t_Array u8 v_SIZE) v_N = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(t_KeccakState v_N v_T & t_Array (t_Array u8 v_SIZE) v_N) =
    squeeze_next_block v_N #v_T v_RATE v_SIZE s out (sz 3 *! v_RATE <: usize)
  in
  let s:t_KeccakState v_N v_T = tmp0 in
  let out:t_Array (t_Array u8 v_SIZE) v_N = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(t_KeccakState v_N v_T & t_Array (t_Array u8 v_SIZE) v_N) =
    squeeze_next_block v_N #v_T v_RATE v_SIZE s out (sz 4 *! v_RATE <: usize)
  in
  let s:t_KeccakState v_N v_T = tmp0 in
  let out:t_Array (t_Array u8 v_SIZE) v_N = tmp1 in
  let _:Prims.unit = () in
  s, out <: (t_KeccakState v_N v_T & t_Array (t_Array u8 v_SIZE) v_N)

let squeeze_first_three_blocks
      (v_N: usize)
      (#v_T: Type0)
      (v_RATE v_SIZE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N)
      (s: t_KeccakState v_N v_T)
      (out: t_Array (t_Array u8 v_SIZE) v_N)
    : (t_KeccakState v_N v_T & t_Array (t_Array u8 v_SIZE) v_N) =
  let out:t_Array (t_Array u8 v_SIZE) v_N = squeeze_first_block v_N #v_T v_RATE v_SIZE s out in
  let tmp0, tmp1:(t_KeccakState v_N v_T & t_Array (t_Array u8 v_SIZE) v_N) =
    squeeze_next_block v_N #v_T v_RATE v_SIZE s out v_RATE
  in
  let s:t_KeccakState v_N v_T = tmp0 in
  let out:t_Array (t_Array u8 v_SIZE) v_N = tmp1 in
  let _:Prims.unit = () in
  let tmp0, tmp1:(t_KeccakState v_N v_T & t_Array (t_Array u8 v_SIZE) v_N) =
    squeeze_next_block v_N #v_T v_RATE v_SIZE s out (sz 2 *! v_RATE <: usize)
  in
  let s:t_KeccakState v_N v_T = tmp0 in
  let out:t_Array (t_Array u8 v_SIZE) v_N = tmp1 in
  let _:Prims.unit = () in
  s, out <: (t_KeccakState v_N v_T & t_Array (t_Array u8 v_SIZE) v_N)
