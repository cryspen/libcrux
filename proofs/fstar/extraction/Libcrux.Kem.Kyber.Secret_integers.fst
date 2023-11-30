module Libcrux.Kem.Kyber.Secret_integers
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_U16 = u16

unfold
let t_U8 = u8

let v_U16_as_U8 (v: u16) : u8 = cast (v <: u16) <: u8

let v_U8_as_U16 (v: u8) : u16 = cast (v <: u8) <: u16

let declassify_U8 (v: u8) : u8 = v
