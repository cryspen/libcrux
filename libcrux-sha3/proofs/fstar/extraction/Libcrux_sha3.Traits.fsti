module Libcrux_sha3.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_sha3.Traits.Internal in
  ()

/// A Keccak Item
/// This holds the internal state and depends on the architecture.
class t_KeccakStateItem (v_Self: Type0) (v_N: usize) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_1179490486619621168:Libcrux_sha3.Traits.Internal.t_KeccakItem
    v_Self v_N
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (v_N: usize)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_sha3.Traits.Internal.t_KeccakItem v_T v_N)
    : t_KeccakStateItem v_T v_N = { _super_1179490486619621168 = FStar.Tactics.Typeclasses.solve }
