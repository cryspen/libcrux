module Libcrux_sha3.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// A Keccak Item
/// This holds the internal state and depends on the architecture.
val t_KeccakStateItem (v_Self: Type0) (v_N: usize) : Type0

(*
[@@@ FStar.Tactics.Typeclasses.no_method]_super_7919791445461910775:Libcrux_sha3.Traits.Internal.t_KeccakItem
    v_Self v_N
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (v_N: usize)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_sha3.Traits.Internal.t_KeccakItem v_T v_N)
    : t_KeccakStateItem v_T v_N =
  { _super_7919791445461910775 = FStar.Tactics.Typeclasses.solve; __marker_trait = () }
*)