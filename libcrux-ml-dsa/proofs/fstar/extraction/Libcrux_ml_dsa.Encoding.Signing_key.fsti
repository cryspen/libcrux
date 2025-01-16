module Libcrux_ml_dsa.Encoding.Signing_key
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

val generate_serialized
      (#v_SIMDUnit #v_Shake256: Type0)
      {| i2: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
      {| i3: Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256 |}
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (error_ring_element_size: usize)
      (seed_matrix seed_signing verification_key: t_Slice u8)
      (s1_2_ t0: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (signing_key_serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)
