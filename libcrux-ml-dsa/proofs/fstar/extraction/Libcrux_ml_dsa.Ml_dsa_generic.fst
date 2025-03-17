module Libcrux_ml_dsa.Ml_dsa_generic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  ()

/// This corresponds to line 6 in algorithm 7 in FIPS 204 (line 7 in algorithm
/// 8, resp.).
/// If `domain_separation_context` is supplied, applies domain
/// separation and length encoding to the context string,
/// before appending the message (in the regular variant) or the
/// pre-hash OID as well as the pre-hashed message digest. Otherwise,
/// it is assumed that `message` already contains domain separation
/// information.
/// In FIPS 204 M' is the concatenation of the domain separated context, any
/// potential pre-hash OID and the message (or the message pre-hash). We do not
/// explicitely construct the concatenation in memory since it is of statically unknown
/// length, but feed its components directly into the incremental XOF.
/// Refer to line 10 of Algorithm 2 (and line 5 of Algorithm 3, resp.) in [FIPS
/// 204](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf#section.5)
/// for details on the domain separation for regular ML-DSA. Line
/// 23 of Algorithm 4 (and line 18 of Algorithm 5,resp.) describe domain separation for the HashMl-DSA
/// variant.
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
    : t_Array u8 (mk_usize 64) =
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
