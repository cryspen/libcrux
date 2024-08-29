module BitVec.Intrinsics

open Core
open Rust_primitives
open FStar.Mul

open FStar.FunctionalExtensionality

let mk_bv #len (f: (i:nat{i < len}) -> bit) = on (i:nat {i < len}) f

let mm256_slli_epi16 (shift: nat {shift <= 16}) (vec: bit_vec 256): bit_vec 256
  = mk_bv (fun i -> let nth_bit = i % 16 in
                 if i >= shift then vec (i - shift) else 0)

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

let mm_packs_epi16 (a b: bit_vec 128): bit_vec 128
  = mk_bv (fun i ->
      let nth_block = i / 8 in
      let offset8 = nth_block * 8 in
      let offset16' = nth_block * 16 in
      let offset16 = offset16' % 128 in
      let vec: bit_vec 128 = if offset16 < 128 then a else b in
      saturate8 (mk_bv (fun j -> vec (offset16 + j))) (i - offset8)
    )

let mm_movemask_epi8_bv (a: bit_vec 128): bit_vec 128
  = mk_bv (fun j ->
             if j < 16
             then a ((j * 8) + 7)
             else 0
          )

let mm_movemask_epi8 (a: bit_vec 128): i32
  = bit_vec_to_int_t 32 (mk_bv (fun i -> a i))

