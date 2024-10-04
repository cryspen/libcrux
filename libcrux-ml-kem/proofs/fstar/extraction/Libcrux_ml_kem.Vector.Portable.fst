module Libcrux_ml_kem.Vector.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Portable.Vector_type in
  ()

let bytes_to_i16 (bytes: t_Slice u8) =
  ((cast (bytes.[ sz 0 ] <: u8) <: i16) <<! 8l <: i16) |. (cast (bytes.[ sz 1 ] <: u8) <: i16)

let i16_to_be_bytes (x: i16) =
  let list = [cast (x >>! 8l <: i16) <: u8; cast (x &. 255s <: i16) <: u8] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list 2 list
