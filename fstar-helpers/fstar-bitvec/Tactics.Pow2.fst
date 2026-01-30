/// Provides tools to normalize `pow2`
module Tactics.Pow2

open Core_models
open Tactics.Utils
open FStar.Tactics.V2

/// Expects `t` to be of the shape `pow2 n`, with `n` a literal, returns n
let expect_pow2_literal t: Tac (option int)
    = let?# (f, [x, _]) = expect_app_n t 1 in
      let?# () = expect_free_var f (`%pow2) in
      expect_int_literal x

/// Expects `t` to be of the shape `pow2 n - 1`, with `n` a literal, returns n
let expect_pow2_minus_one_literal t: Tac (option int)
    = let?# (f, [x, _; y, _]) = expect_app_n t 2 in
      let?# () = expect_free_var f (`%op_Subtraction) in
      let?# y = expect_int_literal y in
      let?? () = y = 1 in
      expect_pow2_literal x

/// Fully normalize a term of the shape `pow2 n`, where `n` is a literal
let norm_pow2 (): Tac unit =
  pointwise (fun () -> 
    let _ = let?# (t, _) = expect_lhs_eq_uvar () in
            let?# n = expect_pow2_literal t in
            debug ("Normalized `pow2 " ^ string_of_int n ^ "`");
            Some (norm [iota; zeta_full; reify_; delta; primops; unmeta]) in
    trefl ())

/// Inverse of `pow2`
let rec log2 (n: nat): Tot (option (m: nat {pow2 m == n})) (decreases n)
    = if n = 0 then None
      else if n = 1 then Some 0
      else if n % 2 <> 0 then None
           else match log2 (n / 2) with
                | Some n -> Some (1 + n)
                | None   -> None

/// Rewrite integers in the goal into `pow2 _ - 1` whenever possible
let rewrite_pow2_minus_one () =
   pointwise (fun () -> 
    match let?# (t, _) = expect_lhs_eq_uvar () in
          let?# n = expect_int_literal t in
          if n >= 0 then
            match log2 (n + 1) with
            | Some e -> 
              let rw_lemma (): Lemma (n == pow2 e - 1) = () in
              apply_lemma_rw (quote rw_lemma);
              Some ()
            | _ -> None
         else None
    with None -> trefl () | _ -> ()
   )

// Test
let _ = fun (i: nat) -> assert (pow2 (i + 3) + pow2 10 == pow2 (i + 3) + 1024)
                       by (norm_pow2 (); trefl ())
