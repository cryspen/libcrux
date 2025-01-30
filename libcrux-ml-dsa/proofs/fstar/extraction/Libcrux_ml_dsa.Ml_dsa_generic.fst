module Libcrux_ml_dsa.Ml_dsa_generic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  ()

let derive_message_representative
      (#v_Shake256Xof: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256Xof)
      (verification_key_hash: t_Slice u8)
      (domain_separation_context:
          Core.Option.t_Option Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext)
      (message: t_Slice u8)
      (message_representative: t_Array u8 (mk_usize 64))
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 verification_key_hash <: usize) =. mk_usize 64
            <:
            bool)
      in
      ()
  in
  let shake:v_Shake256Xof =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_init #v_Shake256Xof #FStar.Tactics.Typeclasses.solve ()
  in
  let shake:v_Shake256Xof =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb #v_Shake256Xof
      #FStar.Tactics.Typeclasses.solve
      shake
      verification_key_hash
  in
  let shake:v_Shake256Xof =
    match
      domain_separation_context
      <:
      Core.Option.t_Option Libcrux_ml_dsa.Pre_hash.t_DomainSeparationContext
    with
    | Core.Option.Option_Some domain_separation_context ->
      let shake:v_Shake256Xof =
        Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb #v_Shake256Xof
          #FStar.Tactics.Typeclasses.solve
          shake
          ((let list =
                [
                  cast (Core.Option.impl__is_some #(t_Array u8 (mk_usize 11))
                        (Libcrux_ml_dsa.Pre_hash.impl_1__pre_hash_oid domain_separation_context
                          <:
                          Core.Option.t_Option (t_Array u8 (mk_usize 11)))
                      <:
                      bool)
                  <:
                  u8
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
            <:
            t_Slice u8)
      in
      let shake:v_Shake256Xof =
        Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb #v_Shake256Xof
          #FStar.Tactics.Typeclasses.solve
          shake
          ((let list =
                [
                  cast (Core.Slice.impl__len #u8
                        (Libcrux_ml_dsa.Pre_hash.impl_1__context domain_separation_context
                          <:
                          t_Slice u8)
                      <:
                      usize)
                  <:
                  u8
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
            <:
            t_Slice u8)
      in
      let shake:v_Shake256Xof =
        Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb #v_Shake256Xof
          #FStar.Tactics.Typeclasses.solve
          shake
          (Libcrux_ml_dsa.Pre_hash.impl_1__context domain_separation_context <: t_Slice u8)
      in
      (match
          Libcrux_ml_dsa.Pre_hash.impl_1__pre_hash_oid domain_separation_context
          <:
          Core.Option.t_Option (t_Array u8 (mk_usize 11))
        with
        | Core.Option.Option_Some pre_hash_oid ->
          Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb #v_Shake256Xof
            #FStar.Tactics.Typeclasses.solve
            shake
            (pre_hash_oid <: t_Slice u8)
        | _ -> shake)
    | _ -> shake
  in
  let shake:v_Shake256Xof =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_absorb_final #v_Shake256Xof
      #FStar.Tactics.Typeclasses.solve
      shake
      message
  in
  let tmp0, tmp1:(v_Shake256Xof & t_Array u8 (mk_usize 64)) =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_squeeze #v_Shake256Xof
      #FStar.Tactics.Typeclasses.solve
      shake
      message_representative
  in
  let shake:v_Shake256Xof = tmp0 in
  let message_representative:t_Array u8 (mk_usize 64) = tmp1 in
  let _:Prims.unit = () in
  message_representative
