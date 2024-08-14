module Libcrux_ml_kem.Ind_cca.Unpacked
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Traits in
  ()

/// An unpacked ML-KEM IND-CCA Private Key
type t_MlKemPrivateKeyUnpacked
  (v_K: usize) (v_Vector: Type0) {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = {
  f_ind_cpa_private_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector;
  f_implicit_rejection_value:t_Array u8 (sz 32)
}

/// An unpacked ML-KEM IND-CCA Private Key
type t_MlKemPublicKeyUnpacked
  (v_K: usize) (v_Vector: Type0) {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = {
  f_ind_cpa_public_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector;
  f_public_key_hash:t_Array u8 (sz 32)
}

/// An unpacked ML-KEM KeyPair
type t_MlKemKeyPairUnpacked
  (v_K: usize) (v_Vector: Type0) {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = {
  f_private_key:t_MlKemPrivateKeyUnpacked v_K v_Vector;
  f_public_key:t_MlKemPublicKeyUnpacked v_K v_Vector
}
