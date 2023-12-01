module Libcrux.Kem.Kyber.Secret_integers
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_I16 = i16

unfold
let t_I32 = i32

unfold
let t_I64 = i64

unfold
let t_U16 = u16

unfold
let t_U8 = u8

let v_I64_as_I32 (v: i64) : i32 = cast (v <: i64) <: i32

let v_I64_from_I32 (v: i32) : i64 = Core.Convert.f_from v

let v_U16_as_I16 (v: u16) : i16 = cast (v <: u16) <: i16

let v_U16_as_U8 (v: u16) : u8 = cast (v <: u16) <: u8

let v_U8_as_U16 (v: u8) : u16 = cast (v <: u8) <: u16

let declassify_I16 (v: i16) : i16 = v

let declassify_I32 (v: i32) : i32 = v

let declassify_U8 (v: u8) : u8 = v
