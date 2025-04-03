module Minicore.Abstractions.Bitvec
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Minicore.Abstractions.Funarr in
  ()

noeq

/// A fixed-size bit vector type.
/// `BitVec<N>` is a specification-friendly, fixed-length bit vector that internally
/// stores an array of [`Bit`] values, where each `Bit` represents a single binary digit (0 or 1).
/// This type provides several utility methods for constructing and converting bit vectors:
/// The [`Debug`] implementation for `BitVec` pretty-prints the bits in groups of eight,
/// making the bit pattern more human-readable. The type also implements indexing,
/// allowing for easy access to individual bits.
type t_BitVec (v_N: u64) =
  | BitVec : Minicore.Abstractions.Funarr.t_FunArray v_N Minicore.Abstractions.Bit.t_Bit
    -> t_BitVec v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': v_N: u64 -> Core.Clone.t_Clone (t_BitVec v_N)

let impl_1 (v_N: u64) = impl_1' v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': v_N: u64 -> Core.Marker.t_Copy (t_BitVec v_N)

let impl (v_N: u64) = impl' v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': v_N: u64 -> Core.Marker.t_StructuralPartialEq (t_BitVec v_N)

let impl_3 (v_N: u64) = impl_3' v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': v_N: u64 -> Core.Cmp.t_PartialEq (t_BitVec v_N) (t_BitVec v_N)

let impl_4 (v_N: u64) = impl_4' v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': v_N: u64 -> Core.Cmp.t_Eq (t_BitVec v_N)

let impl_2 (v_N: u64) = impl_2' v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6 (v_N: u64) : Core.Ops.Index.t_Index (t_BitVec v_N) u64 =
  {
    f_Output = Minicore.Abstractions.Bit.t_Bit;
    f_index_pre = (fun (self_: t_BitVec v_N) (index: u64) -> index <. v_N);
    f_index_post
    =
    (fun (self: t_BitVec v_N) (index: u64) (out: Minicore.Abstractions.Bit.t_Bit) -> true);
    f_index
    =
    fun (self: t_BitVec v_N) (index: u64) ->
      Minicore.Abstractions.Funarr.impl_5__get v_N #Minicore.Abstractions.Bit.t_Bit self._0 index
  }

/// An F* attribute that indiquates a rewritting lemma should be applied
let v_REWRITE_RULE: Prims.unit = ()

let impl_9__from_fn
    (v_N: u64)
    (f: (i: u64 {v i < v v_N}) -> Minicore.Abstractions.Bit.t_Bit)
    : t_BitVec v_N = 
    BitVec(Minicore.Abstractions.Funarr.impl_5__from_fn v_N f)

open FStar.FunctionalExtensionality
let impl_9__pointwise
    (v_N: u64) (f: t_BitVec v_N)
    (#[Minicore.Abstractions.Funarr.e_pointwise_apply_mk_term (v v_N) (fun (i:nat{i < v v_N}) -> f._0 (mk_u64 i))] def: (n: nat {n < v v_N}) -> Minicore.Abstractions.Bit.t_Bit)
    : t_BitVec v_N
    = impl_9__from_fn v_N (on (i: u64 {v i < v v_N}) (fun i -> def (v i)))

let extensionality' (#a: Type) (#b: Type) (f g: FStar.FunctionalExtensionality.(a ^-> b))
  : Lemma (ensures (FStar.FunctionalExtensionality.feq f g <==> f == g))
  = ()

let do_not_reduce #t (x: t): t = x

open FStar.Tactics.V2
#push-options "--z3rlimit 80 --admit_smt_queries true"
let impl_7__rewrite_pointwise (x: t_BitVec (mk_u64 128))
: Lemma (x == do_not_reduce (impl_9__pointwise (mk_u64 128) x)) =
    let a = x._0 in
    let b = (impl_9__pointwise (mk_u64 128) x)._0 in
    assert_norm (FStar.FunctionalExtensionality.feq a b);
    extensionality' a b

let impl_8__rewrite_pointwise (x: t_BitVec (mk_u64 256))
: Lemma (x == do_not_reduce (impl_9__pointwise (mk_u64 256) x)) =
    let a = x._0 in
    let b = (impl_9__pointwise (mk_u64 256) x)._0 in
    assert_norm (FStar.FunctionalExtensionality.feq a b);
    extensionality' a b
#pop-options

let postprocess_rewrite_helper (rw_lemma: term) (): Tac unit = with_compat_pre_core 1 (fun () -> 
    let debug_mode = ext_enabled "debug_bv_postprocess_rewrite" in
    let crate = match cur_module () with | crate::_ -> crate | _ -> fail "Empty module name" in
    // Remove indirections
    norm [primops; iota; delta_namespace [crate; "Libcrux_intrinsics"]; zeta_full];
    // Rewrite call chains
    let lemmas = FStar.List.Tot.map (fun f -> pack_ln (FStar.Stubs.Reflection.V2.Data.Tv_FVar f)) (lookup_attr (`v_REWRITE_RULE) (top_env ())) in
    l_to_r lemmas;
    /// Get rid of casts
    norm [primops; iota; delta_namespace ["Rust_primitives"; "Prims.pow2"]; zeta_full];
    if debug_mode then print ("[postprocess_rewrite_helper] lemmas = " ^ term_to_string (quote lemmas));
    if debug_mode then dump "[postprocess_rewrite_helper] After applying lemmas";
    // Apply pointwise rw
    let rec pointwise_rw (): Tac unit = 
      let done = alloc false in
      ctrl_rewrite TopDown (fun t -> 
          let f, _ = collect_app t in
          let matches = match inspect f with | Tv_UInst f _ | Tv_FVar f -> (inspect_fv f) = explode_qn (`%do_not_reduce) | _ -> false in
          //   let s = term_to_string f in
          //   let s = match String.split ['\n'] s with | hd::_ -> hd | _ -> s in
          //   print ("===>>" ^ s);
          //   print ("===>> matches = " ^ string_of_bool matches);
          if matches
          then (false, Skip)
          else if read done then (false, Skip) else (true, Continue)
      ) 
      (fun _ -> (fun () -> apply_lemma_rw rw_lemma; write done true)
      `or_else` trefl);
      if read done
      then pointwise_rw ()
      else ()
    in
    pointwise_rw ();
    
    if debug_mode then dump "[postprocess_rewrite_helper] Rewrote goal";
    // Normalize as much as possible
    norm [primops; iota; delta_namespace ["Core"; crate; "Minicore"; "Libcrux_intrinsics"; "FStar.FunctionalExtensionality"; "Prims.pow2xx"; "Rust_primitives"]; zeta_full];
    if debug_mode then print ("[postprocess_rewrite_helper] first norm done");
    // Compute the last bits
    compute ();
    if debug_mode then dump ("[postprocess_rewrite_helper] compute done");
    // Force full normalization
    norm [primops; iota; delta; zeta_full];
    if debug_mode then dump "[postprocess_rewrite_helper] after full normalization";
    // Solves the goal `<normalized body> == ?u`
    trefl ()
)

let impl_8__postprocess_rewrite = postprocess_rewrite_helper (`impl_8__rewrite_pointwise)
let impl_7__postprocess_rewrite = postprocess_rewrite_helper (`impl_7__rewrite_pointwise)

#push-options "--z3rlimit 50 --split_queries always"

let impl_10__chunked_shift__chunked_shift
      (v_N v_CHUNK v_SHIFTS: u64)
      (bitvec: t_BitVec v_N)
      (shl: Minicore.Abstractions.Funarr.t_FunArray v_SHIFTS i128)
    : Prims.Pure (t_BitVec v_N)
      (requires
        v_CHUNK >. mk_u64 0 &&
        ((Rust_primitives.Hax.Int.from_machine v_CHUNK <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine v_SHIFTS <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) =
        (Rust_primitives.Hax.Int.from_machine v_N <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  impl_9__from_fn v_N
    (fun i ->
        let i:u64 = i in
        let nth_bit:u64 = i %! v_CHUNK in
        let nth_chunk:u64 = i /! v_CHUNK in
        let _:Prims.unit =
          Hax_lib.assert_prop (b2t
              ((Rust_primitives.Hax.Int.from_machine nth_chunk <: Hax_lib.Int.t_Int) <=
                ((Rust_primitives.Hax.Int.from_machine v_SHIFTS <: Hax_lib.Int.t_Int) -
                  (1 <: Hax_lib.Int.t_Int)
                  <:
                  Hax_lib.Int.t_Int)
                <:
                bool))
        in
        let _:Prims.unit = () in
        let _:Prims.unit =
          Hax_lib.assert_prop (b2t
              (((Rust_primitives.Hax.Int.from_machine nth_chunk <: Hax_lib.Int.t_Int) *
                  (Rust_primitives.Hax.Int.from_machine v_CHUNK <: Hax_lib.Int.t_Int)
                  <:
                  Hax_lib.Int.t_Int) <=
                (((Rust_primitives.Hax.Int.from_machine v_SHIFTS <: Hax_lib.Int.t_Int) -
                    (1 <: Hax_lib.Int.t_Int)
                    <:
                    Hax_lib.Int.t_Int) *
                  (Rust_primitives.Hax.Int.from_machine v_CHUNK <: Hax_lib.Int.t_Int)
                  <:
                  Hax_lib.Int.t_Int)
                <:
                bool))
        in
        let _:Prims.unit = () in
        let (shift: i128):i128 = if nth_chunk <. v_SHIFTS then shl.[ nth_chunk ] else mk_i128 0 in
        let local_index:i128 =
          Core.Num.impl_i128__wrapping_sub (cast (nth_bit <: u64) <: i128) shift
        in
        if local_index <. (cast (v_CHUNK <: u64) <: i128) && local_index >=. mk_i128 0
        then
          let local_index:u64 = cast (local_index <: i128) <: u64 in
          let _:Prims.unit =
            Hax_lib.assert_prop (b2t
                ((((Rust_primitives.Hax.Int.from_machine nth_chunk <: Hax_lib.Int.t_Int) *
                      (Rust_primitives.Hax.Int.from_machine v_CHUNK <: Hax_lib.Int.t_Int)
                      <:
                      Hax_lib.Int.t_Int) +
                    (Rust_primitives.Hax.Int.from_machine local_index <: Hax_lib.Int.t_Int)
                    <:
                    Hax_lib.Int.t_Int) <
                  ((Rust_primitives.Hax.Int.from_machine v_SHIFTS <: Hax_lib.Int.t_Int) *
                    (Rust_primitives.Hax.Int.from_machine v_CHUNK <: Hax_lib.Int.t_Int)
                    <:
                    Hax_lib.Int.t_Int)
                  <:
                  bool))
          in
          let _:Prims.unit = () in
          bitvec.[ (nth_chunk *! v_CHUNK <: u64) +! local_index <: u64 ]
        else Minicore.Abstractions.Bit.Bit_Zero <: Minicore.Abstractions.Bit.t_Bit)

#pop-options

let impl_10__chunked_shift
      (v_N v_CHUNK v_SHIFTS: u64)
      (self: t_BitVec v_N)
      (shl: Minicore.Abstractions.Funarr.t_FunArray v_SHIFTS i128)
    : Prims.Pure (t_BitVec v_N)
      (requires
        v_CHUNK >. mk_u64 0 &&
        ((Rust_primitives.Hax.Int.from_machine v_CHUNK <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine v_SHIFTS <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) =
        (Rust_primitives.Hax.Int.from_machine v_N <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = impl_10__chunked_shift__chunked_shift v_N v_CHUNK v_SHIFTS self shl
