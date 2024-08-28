/// Provides tactics around `get_bit _ _ == get_bit _ _` goals
module Tactics.GetBit

open Core
module L = FStar.List.Tot
open FStar.Tactics.V2
open FStar.Tactics.V2.SyntaxHelpers
open FStar.Class.Printable
open FStar.Mul
open FStar.Option

open Tactics.Utils
open Tactics.Pow2

open BitVecEq {}
open Tactics.Seq {norm_index, tactic_list_index}


let norm_machine_int () = Tactics.MachineInts.(transform norm_machine_int_term)

/// Does one round of computation
let compute_one_round (): Tac _ =
   norm [ iota; zeta; reify_
        ; delta_namespace ["FStar"; implode_qn (cur_module ()); "MkSeq"]
        ; primops; unmeta];
   trace "compute_one_round: norm_pow2"        norm_pow2;
   trace "compute_one_round: norm_machine_int" norm_machine_int;
   trace "compute_one_round: norm_index"       norm_index

/// Normalizes up to `get_bit`
let compute': unit -> Tac unit = goal_fixpoint compute_one_round

private let time_tactic_ms (t: 'a -> Tac 'b) (x: 'a): Tac ('b & int)
  = let time0 = curms () in
    let result = t x in
    let time1 = curms () in
    (result, time1 - time0)

private let print_time prefix (t: 'a -> Tac 'b) (x: 'a): Tac 'b
  = let (result, time) = time_tactic_ms t x in
    print (prefix ^ string_of_int (time / 1000) ^ "." ^ string_of_int ((time/100)%10) ^ "s");
    result

/// Proves a goal of the shape `forall (i:nat{i < N}). get_bit ... i == get_bit ... i` (`N` is expected to be a literal)
let prove_bit_vector_equality' (): Tac unit = 
  norm [iota; primops; delta_only [`%bit_vec_of_int_t_array; `%FunctionalExtensionality.on]];
  norm [iota; primops; delta_namespace [implode_qn (cur_module ())]];
  compute_one_round ();
  prove_forall_nat_pointwise (print_time "SMT solved the goal in " (fun _ -> 
    Tactics.Seq.norm_index_minimal ();
    print ("Ask SMT: " ^ term_to_string (cur_goal ()));
    set_rlimit 80;
    let _ = repeat clear_top in
    focus smt_sync
  ))
let prove_bit_vector_equality (): Tac unit = 
  with_compat_pre_core 2 prove_bit_vector_equality'

