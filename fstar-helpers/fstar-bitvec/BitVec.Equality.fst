module BitVec.Equality

open Core_models
open Rust_primitives
open FStar.Mul
open FStar.FunctionalExtensionality

private let mk_bv #len (f: (i:nat{i < len}) -> bit) = on (i:nat {i < len}) f

let rec bv_equality'' #n (bv1 bv2: bit_vec n)
  : r: bool {r <==> feq bv1 bv2}
  = if n = 0 then true 
    else let n' = n - 1 in
         if bv1 n' = bv2 n'
         then 
           (
           let bv1' = mk_bv (fun i -> bv1 i) in
           let bv2' = mk_bv (fun i -> bv2 i) in
           if bv_equality'' #n' bv1' bv2'
           then (
             assert (forall (x: nat{x < n'}). bv1' x == bv1 x);
             assert (forall (x: nat{x < n'}). bv2' x == bv2 x);
             true
           )
           else false
           )
         else false

let bv_equality' #n (bv1 bv2: bit_vec n)
  : r: bool {r <==> bv1 == bv2}
  = extensionality _ _ bv1 bv2;
    bv_equality'' bv1 bv2


let bv_equality #n (bv1 bv2: bit_vec n) = bv_equality' bv1 bv2

let bv_equality_elim #n (bv1 bv2: bit_vec n)
  : Lemma (requires bv_equality bv1 bv2)
          (ensures  bv1 == bv2)
  = ()
let bv_equality_intro #n (bv1 bv2: bit_vec n)
  : Lemma (requires bv1 == bv2)
          (ensures  bv_equality bv1 bv2)
  = ()

let rewrite n (bv1: bit_vec n)
  : Lemma (bv_equality #n bv1 bv1 == true)
  = ()
