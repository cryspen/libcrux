module Tactics.Utils

open Core
module L = FStar.List.Tot
open FStar.Tactics.V2
open FStar.Tactics.V2.SyntaxHelpers
open FStar.Class.Printable
open FStar.Mul
open FStar.Option


let (let?#) (x: option 'a) (f: 'a -> Tac (option 'b)): Tac (option 'b)
  = match x with
  | Some x -> f x
  | None   -> None

let ( let?? ) (x: bool) (f: unit -> Tac (option 'a)): Tac (option 'a)
  = if x then f () else None

let expect_int_literal (t: term): Tac (option int) =
    match inspect_unascribe t with
    | Tv_Const (C_Int n) -> Some n
    | _ -> None

let expect_fvar (t: term): Tac (option string) =
    match t with
    | Tv_UInst fv _
    | Tv_FVar fv -> Some (implode_qn (inspect_fv fv))
    | _ -> None

let expect_free_var (t: term) (fv: string): Tac (option unit) =
    let?# fv' = expect_fvar t in
    if fv = fv' then Some () else None

let expect_lhs_eq_rhs_term t = 
    match term_as_formula t with
    | Comp (Eq typ) lhs rhs -> 
      let typ = match typ with | None -> `_ | Some typ -> typ in
      Some (lhs, rhs, typ)
    | _ -> None
    
// let expect_forall t =
//     match term_as_formula t with
//     | Comp (Eq typ) lhs rhs -> 
//       let typ = match typ with | None -> `_ | Some typ -> typ in
//       Some (lhs, rhs, typ)
//     | _ -> None

let expect_lhs_eq_rhs () = 
    expect_lhs_eq_rhs_term (cur_goal ())

let expect_lhs_eq_uvar () = 
    match expect_lhs_eq_rhs () with
    | Some (lhs, rhs, typ) -> 
      ( match rhs with | Tv_Uvar _ _ -> Some (lhs, typ) | _ -> None )
    | _ -> None

let expect_app_n t n: Tac (option (term & (l: list _ {L.length l == n}))) =
    let (head, args) = collect_app t in
    if L.length args = n
    then Some (head, args)
    else None

private exception ForceRevert
let revert_if_none (f: unit -> Tac (option 'a)): Tac (option 'a)
  = try match f () with Some x -> Some x 
                      | None -> raise ForceRevert
    with | ForceRevert -> None | e -> raise e

/// Collects an application whose head is a free variable
let collect_app_hd t: Tac (option (string & list argv))
  = let (hd, args) = collect_app t in
    let?# fv = expect_fvar hd in
    Some (fv, args)

let rec repeatWhile (f: unit -> Tac bool): Tac unit
  = if f () then repeatWhile f


let fail' msg = dump msg; fail msg

exception Restore
let dump' (msg: string): Tac unit
    = try set_smt_goals [];
          iterAll (fun _ -> let _ = repeat clear_top in ());
          dump msg;
          raise Restore
      with | _ -> ()

let expect (msg: string) (x: option 'a): Tac 'a
  = match x with
  | None -> 
    dump' ("Expected " ^ msg);
    fail ("Expected " ^ msg)
  | Some x -> x


let statement_of_lemma (lemma: term) =
  let _, comp = collect_arr (tc (cur_env ()) lemma) in
  match inspect_comp comp with
  | C_Total x
  | C_Lemma _ x _ -> (
      match x with
      | Tv_Abs _ x -> `(squash (`#x))
      | _ -> `(squash (`#x))
    )
  | _ -> fail "statement_of_lemma: supports only Tot and Lemma"

let weaken_eq2_lemma (u: Type) (t: Type {subtype_of t u}) (p q: t) ()
  : Lemma (requires ( == ) #u p q)
          (ensures  ( == ) #t p q)
  = ()
  
let apply_lemma_rw_eqtype (lemma: term): Tac unit
  = try
      apply_lemma_rw lemma 
    with
    | e -> match
            let stmt = statement_of_lemma lemma in
            let?# (lemma_lhs, lemma_rhs, type_lemma') = expect_lhs_eq_rhs_term stmt in
            let?# (goal_lhs, goal_rhs, type_goal') = expect_lhs_eq_rhs () in
            let type_lemma = norm_term [delta; iota; primops] type_lemma' in
            let type_goal  = norm_term [delta; iota; primops] type_goal'  in
            if term_eq type_lemma type_goal
            then None
            else
              ( print "######## Warning: apply_lemma_rw, rewrite equalities with different type";
                print ("######## Your lemma has eq over type " ^ term_to_string type_lemma);
                print ("######## Your goal has eq over type " ^ term_to_string type_goal);
                print ("######## Trying to weaken the type of the goal.");
                apply_lemma (
                  `weaken_eq2_lemma
                    (`#type_lemma') (`#type_goal')
                    (`#goal_lhs) (`#goal_rhs)
                );
                apply_lemma_rw lemma;
                Some ()
              )
          with | None -> raise e
               | Some () -> ()


let rewrite_lhs (): Tac _ =
  let (lhs, _, _) = expect_lhs_eq_rhs () |> expect "a goal `<lhs> == <rhs>` (rewrite_lhs)" in
  let uvar = fresh_uvar (Some (tc (cur_env ()) lhs)) in
  tcut (`squash (`#lhs == `#uvar))
  
