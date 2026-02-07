module Tactics.Utils

open Core_models
open FStar.Option
module L = FStar.List.Tot
open FStar.Tactics.V2
open FStar.Tactics.V2.SyntaxHelpers
open FStar.Class.Printable
open FStar.Mul

(*** Let operators *)
let (let?#) (x: option 'a) (f: 'a -> Tac (option 'b)): Tac (option 'b)
  = match x with
  | Some x -> f x
  | None   -> None

let ( let?? ) (x: bool) (f: unit -> Tac (option 'a)): Tac (option 'a)
  = if x then f () else None

(*** Debug helpers *)
/// Dump before failing (in some cases, exception cathing messes with
/// `fail`)
let fail' msg = dump msg; fail msg

exception Restore
/// Dumps a goal with a minimal number of binders in the environment
let dump' (msg: string): Tac unit
    = try set_smt_goals [];
          iterAll (fun _ -> let _ = repeat clear_top in ());
          dump msg;
          raise Restore
      with | _ -> ()

(*** `option _` helpers *)
/// Executes `f`, if it fails, execute `g`. Like `or_else`, but returns
/// a chunk.
let ( ||> ) (f: 'a -> Tac 'b) (g: 'a -> Tac 'b) (a: 'a): Tac 'b
  = try f a with | _ -> g a

exception ExpectedSome
/// Unwraps an option, throws `ExpectedSome` if the option is `None`
let unwrap (x: option 'a): Tac 'a 
  = match x with
  | Some x -> x
  | None -> raise ExpectedSome

/// Expects an option to be `None`, otherwise throws an error
let expect (msg: string) (x: option 'a): Tac 'a
  = match x with
  | None -> dump' ("Expected " ^ msg);
           fail ("Expected " ^ msg)
  | Some x -> x

(*** misc. utils *)
/// Reverse function composition (in Tac)
unfold let (>>>) (f: 'a -> Tac 'b) (g: 'b -> Tac 'c) (x: 'a): Tac 'c
  = g (f x)
/// Function composition (in Tac)
unfold let (∘) (f: 'b -> Tac 'c) (g: 'a -> Tac 'b): 'a -> Tac 'c
  = g >>> f


let trace (fun_name: string) (t: unit -> Tac 'b) =
  print (fun_name ^ ": enter");
  let result = 
    try t ()
    with | e -> (print (fun_name ^ ": exit (with an exception!)"); raise e)
  in 
  print (fun_name ^ ": exit");
  result

(*** control utils *)
/// Repeats a tactic `f` until the goal is stable
let goal_fixpoint (f: unit -> Tac unit): unit -> Tac unit
  = let rec aux (): Tac _ =
        let goal0 = cur_goal () in
        f ();
        let goal1 = cur_goal () in
        if not (term_eq goal0 goal1) then aux ()
    in aux

private exception DoRefl
let some_or_refl (f: unit -> Tac (option unit))
  = or_else (fun _ -> match f () with | None -> raise DoRefl | _ -> ()) trefl

/// Runs `f` on each subterms for rewrite. If `f` is `None` or raises
/// an error, applies `trefl`.
let pointwise_or_refl (f: unit -> Tac (option unit))
  = pointwise (fun _ -> some_or_refl f)

let rec repeatWhile (f: unit -> Tac bool): Tac unit
  = if f () then repeatWhile f

(*** `expect_*` combinators *)
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

let expect_forall t: Tac _ =
    match term_as_formula t with
    | Forall bv typ phi -> Some (bv, typ, phi)
    | _ -> None

(*** Rewrite utils *)
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

/// `apply_lemma_rw` doesn't work if the goal is `(==) #t ... (?u ...)` while the lemma is `(==) #u .. (?u ....)`. `apply_lemma_rw_eqtype` fixes some of those case, and warns about it.
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

/// Rewrites LHS of an equality: on goal `squash (x == y)`, it will add `squash (x == (?u ...))`.
let rewrite_lhs (): Tac _ =
  let (lhs, _, _) = expect_lhs_eq_rhs () |> expect "a goal `<lhs> == <rhs>` (rewrite_lhs)" in
  let uvar = fresh_uvar (Some (tc (cur_env ()) lhs)) in
  tcut (`squash (`#lhs == `#uvar))
  
/// Rewrites RHS of an equality: on goal `squash (x == y)`, it will add `squash (y == (?u ...))`.
let rewrite_rhs (): Tac _ =
  let (_, rhs, _) = expect_lhs_eq_rhs () |> expect "a goal `<lhs> == <rhs>` (rewrite_rhs)" in
  let uvar = fresh_uvar (Some (tc (cur_env ()) rhs)) in
  tcut (`squash (`#rhs == `#uvar))

open FStar.Tactics
(*** Unification *)
(** Unifies `t` with `fn x1 ... xN`, where `x1` and `xN` are
unification variables. This returns a list of terms to substitute `x1`
... `xN` with. You probably want `norm_steps` to be `[delta_only
[`%the_name_of_function_fn]]` *)
exception UnifyAppReturn of (option (list term))
let unify_app (t fn: term) norm_steps: Tac (option (list term))
  = let (* Tactic types are confusing, seems like we need V1 here *)
        open FStar.Tactics.V1 in
    let bds = fst (collect_arr_bs (tc (cur_env ()) fn)) in
    try
      let _fake_goal = 
        (* create a goal `b1 -> ... -> bn -> squash True` *)
        let trivial = `squash True in
        let trivial_comp = pack_comp (C_Total trivial) in
        unshelve (fresh_uvar (Some (match bds with | [] -> trivial | _ -> mk_arr bds trivial_comp)))
      in
      (* get back the binders `b1`, ..., `bn` *)
      let bds = intros () in
      let args = FStar.Tactics.Util.map (fun (b: binder) -> b <: term) bds in
      let norm_term = norm_term (hnf::norm_steps) in
      let fn, t = norm_term (mk_e_app fn args), norm_term t in
      let fn = `(((`#fn), ())) in
      let dummy_var = fresh_namedv_named "dummy_var" in
      let t = `(((`#t), (`#dummy_var))) in
      let vars = map (fun b -> 
        let b = inspect_binder b in
        let {bv_index = uniq; bv_ppname = ppname} = inspect_bv b.binder_bv in
        let sort = b.binder_sort in
        let nv: namedv_view = {uniq; ppname; sort = seal sort} in
        (FStar.Reflection.V2.pack_namedv nv, sort)
      ) bds in
      let vars = 
        List.Tot.append
          vars 
          [(FStar.Reflection.V2.pack_namedv dummy_var, `())] 
      in
      let?# substs = fst (try_unify (cur_env ()) vars fn t) in
      raise (UnifyAppReturn (
        if List.Tot.length substs <> List.Tot.length bds + 1
        then (print ("unify_app: WARNING: inconsistent lengths: " ^ string_of_int (List.Tot.length substs) ^ " - 1 VS " ^ string_of_int (List.Tot.length bds + 1)); None)
        else (
          match substs with
          | [] -> None
          | _::substs -> Some (List.Tot.rev (map (fun (_, t) -> t) substs))
        )))
    with | UnifyAppReturn result -> result
         | e -> raise e

(*** Logging and time *)
let time_tactic_ms (t: 'a -> Tac 'b) (x: 'a): Tac ('b & int)
  = let time0 = curms () in
    let result = t x in
    let time1 = curms () in
    (result, time1 - time0)

let print_time prefix (t: 'a -> Tac 'b) (x: 'a): Tac 'b
  = let (result, time) = time_tactic_ms t x in
    print (prefix ^ string_of_int (time / 1000) ^ "." ^ string_of_int ((time/100)%10) ^ "s");
    result

(*** Unroll forall goals *)
let _split_forall_nat
  (upper_bound: pos)
  ($p: (i:nat{i < upper_bound}) -> Type0)
  : Lemma (requires (if upper_bound = 0 then True
                     else p (upper_bound - 1) /\ (forall (i:nat{i < upper_bound - 1}). p i)))
          (ensures forall (i:nat{i < upper_bound}). p i)
  = ()


let focus_first_forall_goal (t : unit -> Tac unit) : Tac unit =
  let goals = goals () in
  let found_goal = alloc false in
  iterAll (fun _ -> 
    (match expect_forall (cur_goal ()) with
    | Some _ ->
      if read found_goal
      then ()
      else begin
        write found_goal true;
        t ();
        ()
      end
    | _ -> 
      ())
  );
  if not (read found_goal) then t ()

/// Proves `forall (i:nat{i < bound})` for `bound` being a concrete int
let rec prove_forall_nat_pointwise (tactic: unit -> Tac unit): Tac unit
  = focus_first_forall_goal (fun _ -> 
      let _ =
        (* hacky way of printing the progress *)
        let goal = term_to_string (cur_goal ()) in
        let goal = match String.split ['\n'] goal with
                   | s::_ -> s | _ -> "" in
        print ("prove_forall_pointwise: " ^ goal ^ "...")
      in
      apply_lemma (`_split_forall_nat);
      trivial `or_else` (fun _ -> 
        if try norm [primops];
               split ();
               true
           with | e -> false
        then (
          tactic ();
          prove_forall_nat_pointwise tactic
        )
      )
    )

#push-options "--compat_pre_core 2"
private let _example (phi: int -> Type0) (proof: (i:int -> Lemma (phi i))) = 
  assert (forall (i: nat {i < 40}). phi i)
      by (
        prove_forall_nat_pointwise (fun _ -> 
          apply_lemma (quote proof)
        )
      )
#pop-options
