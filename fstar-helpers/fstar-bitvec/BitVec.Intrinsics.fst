module BitVec.Intrinsics

open Core
open Rust_primitives
open FStar.Mul

open FStar.FunctionalExtensionality

let mk_bv #len (f: (i:nat{i < len}) -> bit) = on (i:nat {i < len}) f

let mm256_slli_epi16 (shift: nat {shift <= 16}) (vec: bit_vec 256): bit_vec 256
  = mk_bv (fun i -> let nth_bit = i % 16 in
                 if nth_bit >= shift 
                 then vec (i - shift)
                 else 0)

let mm256_castsi256_si128 (vec: bit_vec 256): bit_vec 128
  = mk_bv (fun i -> vec i)
let mm256_extracti128_si256 (control: nat {control == 1}) (vec: bit_vec 256): bit_vec 128
  = mk_bv (fun i -> vec (i + 128))

private let saturate8 (v: bit_vec 16): bit_vec 8
  = let on_upper_bits (+) (f: (n:nat{n >= 8 && n <= 15}) -> _) 
        = f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 
    in
    let any1 = on_upper_bits ( ||  ) (fun i -> v i = 1) in
    let all1 = on_upper_bits ( && ) (fun i -> v i = 1) in
    let negative = v 15 = 1 in
    mk_bv (fun i ->
      let last_bit = i = 7 in
      if negative
      then if last_bit 
           then 1
           else if all1
                then v i
                else 0
      else if any1
           then if last_bit
                then 0
                else 1
           else v i
    )

let mm_movemask_epi8_bv (a: bit_vec 128): bit_vec 128
  = mk_bv (fun j ->
             if j < 16
             then a ((j * 8) + 7)
             else 0
          )

let mm_movemask_epi8 (a: bit_vec 128): i32
  = bit_vec_to_int_t 32 (mk_bv (fun i -> mm_movemask_epi8_bv a i))

let mm256_set_epi16 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15: i16)
  : bit_vec 256
  = mk_bv (fun i ->
      let offset = i % 16 in
      match i / 16 with
      |  0 -> get_bit  x0 (sz offset)
      |  1 -> get_bit  x1 (sz offset)
      |  2 -> get_bit  x2 (sz offset)
      |  3 -> get_bit  x3 (sz offset)
      |  4 -> get_bit  x4 (sz offset)
      |  5 -> get_bit  x5 (sz offset)
      |  6 -> get_bit  x6 (sz offset)
      |  7 -> get_bit  x7 (sz offset)
      |  8 -> get_bit  x8 (sz offset)
      |  9 -> get_bit  x9 (sz offset)
      | 10 -> get_bit x10 (sz offset)
      | 11 -> get_bit x11 (sz offset)
      | 12 -> get_bit x12 (sz offset)
      | 13 -> get_bit x13 (sz offset)
      | 14 -> get_bit x14 (sz offset)
      | 15 -> get_bit x15 (sz offset)
    )

open FStar.Stubs.Tactics.V2.Builtins
open FStar.Stubs.Tactics.V2
open FStar.Tactics.V2.Derived
open FStar.Tactics.V2

let rec bv_to_string #len (bv: bit_vec len): string
  = if len = 0 then ""
               else string_of_int (bv (len - 1)) 
                  ^ bv_to_string #(len - 1) (mk_bv (fun i -> bv i))

let bv_of_string #len (s: string): Tac (bit_vec len)
  = let l = FStar.String.list_of_string s 
          |> filter (function ' ' | '\n' -> false | _ -> true)
          |> map #_ #bit (function '1' -> 1 <: bit | '0' -> 0 | c -> fail ("expected 0 or 1, got [" ^ String.string_of_char c ^ "]")) in
    if FStar.List.Tot.length l = len
    then mk_bv (fun (i: nat {i < len}) -> List.Tot.index l i)
    else fail ("expected a bv of length " ^ string_of_int len ^ ", got a bv of length " ^ string_of_int (FStar.List.Tot.length l))

let call_native_intrinsic' #ilen name raw_args (bitvecs: list (bit_vec ilen)) : Tac string =
  let bitvecs = List.Tot.map bv_to_string bitvecs in
  let args = List.Tot.append raw_args bitvecs in
  let result = launch_process "bash" ("/tmp/run.sh"::name::args) "" in
  print ("process stdout is [" ^ result ^ "]");
  FStar.String.list_of_string result
    |> filter (function ' ' | '\n' -> false | _ -> true)
    |> String.string_of_list

let call_native_intrinsic #ilen olen name raw_args (bitvecs: list (bit_vec ilen)) : Tac (bit_vec olen) =
  bv_of_string (call_native_intrinsic' #ilen name raw_args bitvecs)

let random_bv len: Tac (bit_vec len) 
  = call_native_intrinsic #1 _ "rand" [string_of_int len] []

let mm_packs_epi16 (a b: bit_vec 128): bit_vec 128
  = mk_bv (fun i ->
      let nth_block = i / 8 in
      let offset8 = nth_block * 8 in
      let offset16' = nth_block * 16 in
      let offset16 = offset16' % 128 in
      let vec: bit_vec 128 = if offset16 < 128 then a else b in
      saturate8 (mk_bv (fun j -> vec (offset16 + j))) (i - offset8)
    )

let tassert (x: bool): Tac unit
  = if x then () else fail "tassert"
