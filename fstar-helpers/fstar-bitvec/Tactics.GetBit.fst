/// Provides tactics around `get_bit _ _ == get_bit _ _` goals
module Tactics.GetBit

open Core_models
module L = FStar.List.Tot
open FStar.Tactics.V2
open FStar.Tactics.V2.SyntaxHelpers
open FStar.Class.Printable
open FStar.Mul
open FStar.Option

open Tactics.Utils
open Tactics.Pow2

open BitVecEq
open Tactics.Seq

/// Does one round of computation
let compute_one_round (): Tac _ =
   norm [ iota; zeta; reify_
          ; delta_namespace [
              "FStar"
            ; "BitVecEq"
            ; implode_qn (cur_module ())
            ; "MkSeq"
            ; `%Rust_primitives.Hax.array_of_list
            ; `%Libcrux_ml_kem.Vector.Portable.Vector_type.__proj__Mkt_PortableVector__item__f_elements
          ]
        ; primops; unmeta];
   trace "compute_one_round: norm_pow2"        norm_pow2;
   trace "compute_one_round: norm_index"       norm_index

/// Normalizes up to `get_bit`
let compute': unit -> Tac unit = goal_fixpoint compute_one_round

/// Proves a goal of the shape `forall (i:nat{i < N}). get_bit ... i == get_bit ... i` (`N` is expected to be a literal)
let prove_bit_vector_equality'' (): Tac unit =
  norm [
    iota;
    primops;
    delta_only [`%bit_vec_of_int_t_array; `%FunctionalExtensionality.on];
    delta_namespace [
      implode_qn (cur_module ());
      "Libcrux_intrinsics.Avx2_extract";
      "BitVec.Intrinsics";
      "BitVecEq";
    ];
  ];
  compute_one_round ();
  prove_forall_nat_pointwise (print_time "SMT solved the goal in " (fun _ -> 
    Tactics.Seq.norm_index_minimal ();
    l_to_r [`bit_vec_to_int_t_lemma];
    print ("Ask SMT: " ^ term_to_string (cur_goal ()));
    focus smt_sync
  ))

let prove_bit_vector_equality' (): Tac unit =
  if lax_on ()
  then iterAll tadmit
  else prove_bit_vector_equality'' ()

let prove_bit_vector_equality (): Tac unit = 
  set_rlimit 100;
  with_compat_pre_core 0 prove_bit_vector_equality'
