module BitVec.Intrinsics.Constants

open Core_models
open Rust_primitives
open FStar.Mul
open FStar.FunctionalExtensionality
open BitVec.Utils
open BitVec.Equality

let mm256_set_epi16 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15: i16)
  : bit_vec 256
  = mk_bv (fun i ->
      let offset = i % 16 in
      match i / 16 with
      |  0 -> get_bit x15 (sz offset)
      |  1 -> get_bit x14 (sz offset)
      |  2 -> get_bit x13 (sz offset)
      |  3 -> get_bit x12 (sz offset)
      |  4 -> get_bit x11 (sz offset)
      |  5 -> get_bit x10 (sz offset)
      |  6 -> get_bit x9 (sz offset)
      |  7 -> get_bit x8 (sz offset)
      |  8 -> get_bit x7 (sz offset)
      |  9 -> get_bit x6 (sz offset)
      | 10 -> get_bit x5 (sz offset)
      | 11 -> get_bit x4 (sz offset)
      | 12 -> get_bit x3 (sz offset)
      | 13 -> get_bit x2 (sz offset)
      | 14 -> get_bit x1 (sz offset)
      | 15 -> get_bit x0 (sz offset)
    )

let madd_rhs (n: nat {n < 16}) = 
  mm256_set_epi16 
    (1s <<! Int32.int_to_t n <: i16) 
    1s 
    (1s <<! Int32.int_to_t n <: i16) 
    1s
    (1s <<! Int32.int_to_t n <: i16) 
    1s 
    (1s <<! Int32.int_to_t n <: i16)
    1s 
    (1s <<! Int32.int_to_t n <: i16) 
    1s 
    (1s <<! Int32.int_to_t n <: i16) 
    1s
    (1s <<! Int32.int_to_t n <: i16) 
    1s 
    (1s <<! Int32.int_to_t n <: i16) 
    1s

open FStar.Tactics.V2

let _ = namedv_view

irreducible let stupid (x: 'a): bit_vec 256 -> bit_vec 256 = admit ()

open Tactics.Utils

open FStar.Tactics

(** Unifies `t` with `fn x1 ... xN`, where `x1` and `xN` are
unification variables. This returns a list of terms to substitute `x1`
... `xN` with.  *)
let unify_app (t fn: term) norm_steps: Tac (option (list term))
  = let bds = fst (collect_arr_bs (tc (cur_env ()) fn)) in
    let _fake_goal = 
      (* create a goal `b1 -> ... -> bn -> squash True` *)
      let trivial = pack_comp (C_Total (`squash True)) in
      unshelve (fresh_uvar (Some (mk_arr bds trivial)))
    in
    (* get back the binders `b1`, ..., `bn` *)
    let bds = intros () in
    let args = map (fun (b: binder) -> b <: term) bds in
    let norm_term = norm_term (hnf::norm_steps) in
    let fn, t = norm_term (mk_e_app fn args), norm_term t in
    let vars = map (fun b -> 
      let b = inspect_binder b in
      let {bv_index = uniq; bv_ppname = ppname} = inspect_bv b.binder_bv in
      let nv: namedv_view = {uniq; ppname; sort = seal (`_)} in
      (FStar.Reflection.V2.pack_namedv nv, b.binder_sort)
    ) bds in
    let?# substs = fst (try_unify (cur_env ()) vars fn t) in
    if List.Tot.length substs <> List.Tot.length bds
    then fail "unify_app: inconsistent lengths";
    (* solve the trivial goal introduced at the begining *)
    trivial ();
    Some (List.Tot.rev (map (fun (_, t) -> t) substs))

irreducible let add (x y: int): int = x + y

let f (a b c d: int): int = add (add (add a b) c) d

// #push-options "--print_full_names --print_implicits --print_bound_var_types"
let _ = assert true by (
  let r = 
    unify_app 
      (quote (f 1 2 3 4))
      (quote f)
      [delta_only [`%f]]
  in
  let s = term_to_string (quote r)
  in
 print s
  )

let test x y (#[(
    let n = fresh_namedv () in
    let y = quote y in
    let y' = `(madd_rhs (`#n)) in
    let n = FStar.Reflection.V2.pack_namedv n in
    let t = match try_unify (cur_env ()) [(n,`(n: nat {n < 16}))] y y' with
    | (Some [v, t'], _) -> 
      `(stupid (`#t'))
    | _ -> `(stupid (`#y)) in
    exact t
)]f: bit_vec 256 -> bit_vec 256) = f x

let xx = fun x -> test x (madd_rhs 12)

irreducible let vec256_to_i16s (bv: bit_vec 256)
  : (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)
  & (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)
  = admit ()

irreducible let rw_vec256_to_i16_ints
  (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15: i16)
  : Lemma (
    vec256_to_i16s (mm256_set_epi16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)
    == ((x0, x1, x2, x3, x4, x5, x6, x7), (x8, x9, x10, x11, x12, x13, x14, x15))
  ) = admit ()

let madd_rhs (n: nat {n < 16}) = 
  mm256_set_epi16 
    (1s <<! Int32.int_to_t n <: i16) 
    1s 
    (1s <<! Int32.int_to_t n <: i16) 
    1s
    (1s <<! Int32.int_to_t n <: i16) 
    1s 
    (1s <<! Int32.int_to_t n <: i16)
    1s 
    (1s <<! Int32.int_to_t n <: i16) 
    1s 
    (1s <<! Int32.int_to_t n <: i16) 
    1s
    (1s <<! Int32.int_to_t n <: i16) 
    1s 
    (1s <<! Int32.int_to_t n <: i16) 
    1s

#push-options "--z3rlimit 100"
let to_madd_rhs (data: (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)
  & (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16))
  : option (n:nat{
    n < 16 /\ (
      let ((x0, x1, x2, x3, x4, x5, x6, x7), (x8, x9, x10, x11, x12, x13, x14, x15)) = data in
      madd_rhs n == mm256_set_epi16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
    )
  })
  = let ((x0, x1, x2, x3, x4, x5, x6, x7), (x8, x9, x10, x11, x12, x13, x14, x15)) = data in
    if   v x0 >= 1
      && v x0 = v x2 && v x0 = v x4  && v x0 = v x6  && v x0 = v x8 
                     && v x0 = v x10 && v x0 = v x12 && v x0 = v x14
      && v x1 = 1    && v x3 = 1     && v x5 = 1     && v x7 = 1 
                     && v x9 = 1    && v x11= 1     && v x13= 1     && v x15= 1
    then match Tactics.Pow2.log2 (v x0 <: nat) with
       | Some coef -> 
         if coef < 16
         then (
           assert (v ((1s <<! Int32.int_to_t coef <: i16)) == v x0);
           Some coef
         ) else None
       | _ -> None
    else None
#pop-options

open FStar.Tactics.V2
[@@FStar.Tactics.V2.postprocess_with (fun _ -> 
  compute ();
  Tactics.Seq.norm_index ();
  compute ();
  fail "x"
)]
let aa =
  let n = 12 in
  let tuple = (
    ( (1s <<! Int32.int_to_t n <: i16) 
    , 1s 
    , (1s <<! Int32.int_to_t n <: i16) 
    , 1s
    , (1s <<! Int32.int_to_t n <: i16) 
    , 1s 
    , (1s <<! Int32.int_to_t n <: i16)
    , 1s),
    ( (1s <<! Int32.int_to_t n <: i16)
    , 1s 
    , (1s <<! Int32.int_to_t n <: i16) 
    , 1s
    , (1s <<! Int32.int_to_t n <: i16) 
    , 1s 
    , (1s <<! Int32.int_to_t n <: i16) 
    , 1s)) in
  let x: nat = match to_madd_rhs tuple with | Some n -> n | None -> 0 in
  x

open Tactics.Utils
open FStar.Tactics.V2
module Visit = FStar.Tactics.Visit

let rec any (f: 'a -> bool) (l: list 'a): bool
    = match l with
    | [] -> false
    | hd::tl -> if f hd
              then true
              else any f tl

exception FoundFreeLocalVar
let is_closed_term (x: term): Tac bool
  = try
      let _ = FStar.Tactics.Visit.visit_tm (
        function 
        | Tv_Var _ | Tv_BVar _ -> raise FoundFreeLocalVar
        | x -> x
        ) x
      in true
    with | FoundFreeLocalVar -> false
         | e -> raise e

let rw_mm256_set_epi16 t = 
  let?# (f, [arg,_]) = expect_app_n t 1 in
  let?# _ = expect_free_var f (`%vec256_to_i16_ints) in
  let?? _ = is_closed_term arg in
  let?# (f, args) = expect_app_n arg 16 in
  let?# _ = expect_free_var f (`%mm256_set_epi16) in
  pointwise' (fun _ ->
    let _ = let?# (lhs, _, _) = expect_lhs_eq_rhs () in
            Some (if any (fun (arg, _) -> term_eq lhs arg) args 
                  then norm [primops; iota; delta; zeta_full]
                  else ())
    in trefl ()
  );
  Some ()

let rec expect_madd_rhs' (bv: bit_vec 256) (n:nat {n < 16})
  : result: option (n: nat {n < 16}) { match result with
                                   | Some n -> bv == madd_rhs n
                                   | _ -> True
                                   }
  = if bv_equality bv (madd_rhs n)
    then ( bv_equality_elim bv (madd_rhs n);
           Some n )
    else if n = 0 then None
         else expect_madd_rhs' bv (n - 1)

irreducible let expect_madd_rhs (bv: bit_vec 256): option (n: nat {n < 16})
  = expect_madd_rhs' bv 15

// let rewrite_expect_madd_rhs
//   (bv: bit_vec 256) (n: nat {n < 16})
//   : Lemma (requires bv == madd_rhs n)
//           (ensures  )
//   = ()
  
