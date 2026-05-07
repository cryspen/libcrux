module Libcrux_kmac
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_sha3.Portable.Incremental in
  let open Libcrux_sha3.Portable.Incremental.Private in
  ()

let kmac_128_ (tag key data customization: t_Slice u8) : (t_Slice u8 & t_Slice u8) =
  let (tmp0: t_Slice u8), (out: t_Slice u8) =
    Libcrux_kmac.Internals.Kmac.compute_kmac (mk_usize 168)
      #(Libcrux_sha3.Portable.Incremental.t_CShakeIncremental (mk_usize 168))
      tag
      (Core_models.Slice.impl__len #u8 tag <: usize)
      key
      (Core_models.Slice.impl__len #u8 key <: usize)
      data
      customization
  in
  let tag:t_Slice u8 = tmp0 in
  let hax_temp_output:t_Slice u8 = out in
  tag, hax_temp_output <: (t_Slice u8 & t_Slice u8)

let kmac_256_ (tag key data customization: t_Slice u8) : (t_Slice u8 & t_Slice u8) =
  let (tmp0: t_Slice u8), (out: t_Slice u8) =
    Libcrux_kmac.Internals.Kmac.compute_kmac (mk_usize 136)
      #(Libcrux_sha3.Portable.Incremental.t_CShakeIncremental (mk_usize 136))
      tag
      (Core_models.Slice.impl__len #u8 tag <: usize)
      key
      (Core_models.Slice.impl__len #u8 key <: usize)
      data
      customization
  in
  let tag:t_Slice u8 = tmp0 in
  let hax_temp_output:t_Slice u8 = out in
  tag, hax_temp_output <: (t_Slice u8 & t_Slice u8)
