module Libcrux_ml_dsa.Ml_dsa_generic_theory
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

(* ============================================================================
   Hand-written companion for `src/ml_dsa_generic.rs` (annotation-uniformity
   sweep Batch 1).  Relocated from the `sign_internal` fstar::before block
   (formerly triplicated into each of the Ml_dsa_{44,65,87}_ instantiation
   modules).  This module is NOT generated -- edit it directly.
   ========================================================================== *)

(* Helper predicate for the sign_internal rejection loop's invariant hint
   clause: once a signature is accepted (`hint = Some h`), its Hamming weight
   stays within MAX_ONES_IN_HINT.  Phrased as a top-level `match` (clean
   context) so the loop invariant references only this atom: an inline
   `Option_Some?._0` projector in the while_loop refinement corrupts the
   post-loop `match hint` pattern typing (the Bundle-encoded
   `Core_models.Option`, F* error 114). *)
let hint_count_bounded
      (#rows: usize)
      (hint: Core_models.Option.t_Option (t_Array (t_Array i32 (mk_usize 256)) rows))
      (m: usize)
    : Type0 =
  match hint with
  | Core_models.Option.Option_Some h ->
    Libcrux_ml_dsa.Encoding.Signature.count_total_ones (h <: t_Slice (t_Array i32 (mk_usize 256))) <= v m
  | Core_models.Option.Option_None  -> Prims.l_True
