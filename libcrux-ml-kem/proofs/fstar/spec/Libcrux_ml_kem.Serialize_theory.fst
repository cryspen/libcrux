module Libcrux_ml_kem.Serialize_theory
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

(* Hand-written proof theory relocated from src/serialize.rs
   `hax_lib::fstar::before` blocks (byte-exact raw-string contents, verified
   verbatim against the green extracted module). Consumed only by that module. *)

(* Reconciliation: at a concrete `dv in {4,5}`, the thin spec wrapper
   `compress_then_serialize_v` unfolds (via `byte_encode_into` + the
   `copy_from_slice s src == src` identity) to exactly the `byte_encode` the
   callees `_4`/`_5` establish. *)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 100"
let lemma_compress_then_serialize_v_eq
      (out_len: usize)
      (dv: usize{v dv == 4 \/ v dv == 5})
      (p: t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256))
    : Lemma (requires v out_len == 32 * v dv)
      (ensures
        Hacspec_ml_kem.Serialize.compress_then_serialize_v out_len p dv ==
        Hacspec_ml_kem.Serialize.byte_encode (mk_usize (32 * v dv)) (mk_usize (256 * v dv))
          (Hacspec_ml_kem.Compress.compress p dv) dv) =
  ()
#pop-options
