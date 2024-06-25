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

val t_KeccakState (v_N: usize) (#v_T: Type0) {| i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N |}
    : Type0

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
val impl_1__new:
    v_N: usize ->
    #v_T: Type0 ->
    {| i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N |} ->
    Prims.unit
  -> Prims.Pure (t_KeccakState v_N v_T) Prims.l_True (fun _ -> Prims.l_True)

val chi
      (v_N: usize)
      (#v_T: Type0)
      {| i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N |}
      (s: t_KeccakState v_N v_T)
    : Prims.Pure (t_KeccakState v_N v_T) Prims.l_True (fun _ -> Prims.l_True)

val iota
      (v_N: usize)
      (#v_T: Type0)
      {| i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N |}
      (s: t_KeccakState v_N v_T)
      (i: usize)
    : Prims.Pure (t_KeccakState v_N v_T) Prims.l_True (fun _ -> Prims.l_True)

val pi
      (v_N: usize)
      (#v_T: Type0)
      {| i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N |}
      (s: t_KeccakState v_N v_T)
    : Prims.Pure (t_KeccakState v_N v_T) Prims.l_True (fun _ -> Prims.l_True)

val squeeze_first_and_last
      (v_N: usize)
      (#v_T: Type0)
      (v_RATE v_SIZE: usize)
      {| i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N |}
      (s: t_KeccakState v_N v_T)
      (out: t_Array (t_Array u8 v_SIZE) v_N)
    : Prims.Pure (t_Array (t_Array u8 v_SIZE) v_N) Prims.l_True (fun _ -> Prims.l_True)

val squeeze_first_block
      (v_N: usize)
      (#v_T: Type0)
      (v_RATE v_SIZE: usize)
      {| i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N |}
      (s: t_KeccakState v_N v_T)
      (out: t_Array (t_Array u8 v_SIZE) v_N)
    : Prims.Pure (t_Array (t_Array u8 v_SIZE) v_N) Prims.l_True (fun _ -> Prims.l_True)

val theta_rho
      (v_N: usize)
      (#v_T: Type0)
      {| i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N |}
      (s: t_KeccakState v_N v_T)
    : Prims.Pure (t_KeccakState v_N v_T) Prims.l_True (fun _ -> Prims.l_True)

val keccakf1600
      (v_N: usize)
      (#v_T: Type0)
      {| i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N |}
      (s: t_KeccakState v_N v_T)
    : Prims.Pure (t_KeccakState v_N v_T) Prims.l_True (fun _ -> Prims.l_True)

val absorb_block
      (v_N: usize)
      (#v_T: Type0)
      (v_RATE: usize)
      {| i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N |}
      (s: t_KeccakState v_N v_T)
      (blocks: t_Array (t_Slice u8) v_N)
    : Prims.Pure (t_KeccakState v_N v_T) Prims.l_True (fun _ -> Prims.l_True)

val absorb_final
      (v_N: usize)
      (#v_T: Type0)
      (v_RATE: usize)
      (v_DELIM: u8)
      {| i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N |}
      (s: t_KeccakState v_N v_T)
      (last: t_Array (t_Slice u8) v_N)
    : Prims.Pure (t_KeccakState v_N v_T) Prims.l_True (fun _ -> Prims.l_True)

val squeeze_last
      (v_N: usize)
      (#v_T: Type0)
      (v_RATE v_SIZE: usize)
      {| i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N |}
      (s: t_KeccakState v_N v_T)
      (out: t_Array (t_Array u8 v_SIZE) v_N)
      (start: usize)
    : Prims.Pure (t_Array (t_Array u8 v_SIZE) v_N) Prims.l_True (fun _ -> Prims.l_True)

val squeeze_next_block
      (v_N: usize)
      (#v_T: Type0)
      (v_RATE v_SIZE: usize)
      {| i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N |}
      (s: t_KeccakState v_N v_T)
      (out: t_Array (t_Array u8 v_SIZE) v_N)
      (start: usize)
    : Prims.Pure (t_KeccakState v_N v_T & t_Array (t_Array u8 v_SIZE) v_N)
      Prims.l_True
      (fun _ -> Prims.l_True)

val keccak
      (v_N: usize)
      (#v_T: Type0)
      (v_RATE v_SIZE: usize)
      (v_DELIM: u8)
      {| i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N |}
      (data: t_Array (t_Slice u8) v_N)
      (out: t_Array (t_Array u8 v_SIZE) v_N)
    : Prims.Pure (t_Array (t_Array u8 v_SIZE) v_N) Prims.l_True (fun _ -> Prims.l_True)

val squeeze_first_five_blocks
      (v_N: usize)
      (#v_T: Type0)
      (v_RATE v_SIZE: usize)
      {| i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N |}
      (s: t_KeccakState v_N v_T)
      (out: t_Array (t_Array u8 v_SIZE) v_N)
    : Prims.Pure (t_KeccakState v_N v_T & t_Array (t_Array u8 v_SIZE) v_N)
      Prims.l_True
      (fun _ -> Prims.l_True)

val squeeze_first_three_blocks
      (v_N: usize)
      (#v_T: Type0)
      (v_RATE v_SIZE: usize)
      {| i1: Libcrux_sha3.Traits.t_KeccakStateItem v_T v_N |}
      (s: t_KeccakState v_N v_T)
      (out: t_Array (t_Array u8 v_SIZE) v_N)
    : Prims.Pure (t_KeccakState v_N v_T & t_Array (t_Array u8 v_SIZE) v_N)
      Prims.l_True
      (fun _ -> Prims.l_True)
