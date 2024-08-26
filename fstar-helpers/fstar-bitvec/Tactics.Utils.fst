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

let expect_lhs_eq_rhs () = 
    match FStar.Tactics.V2.Logic.cur_formula () with
    | Comp (Eq typ) lhs rhs -> 
      let typ = match typ with | None -> `_ | Some typ -> typ in
      Some (lhs, rhs, typ)
    | _ -> None

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
