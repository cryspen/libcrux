module RwLemmas

open Core
module L = FStar.List.Tot
open FStar.Tactics.V2
open FStar.Tactics.V2.SyntaxHelpers
open FStar.Class.Printable
open FStar.Mul
open FStar.Option

open Tactics.Utils
open Tactics.Pow2

open BitVecEq {}

let norm_machine_int () = Tactics.MachineInts.(transform norm_machine_int_term)

#push-options "--z3rlimit 40"
let deserialize_10_int (bytes: t_Array u8 (sz 10)) =
  let r0:i16 =
    (((cast (bytes.[ sz 1 ] <: u8) <: i16) &. 3s <: i16) <<! 8l <: i16) |.
    ((cast (bytes.[ sz 0 ] <: u8) <: i16) &. 255s <: i16)
  in
  let r1:i16 =
    (((cast (bytes.[ sz 2 ] <: u8) <: i16) &. 15s <: i16) <<! 6l <: i16) |.
    ((cast (bytes.[ sz 1 ] <: u8) <: i16) >>! 2l <: i16)
  in
  let r2:i16 =
    (((cast (bytes.[ sz 3 ] <: u8) <: i16) &. 63s <: i16) <<! 4l <: i16) |.
    ((cast (bytes.[ sz 2 ] <: u8) <: i16) >>! 4l <: i16)
  in
  let r3:i16 =
    ((cast (bytes.[ sz 4 ] <: u8) <: i16) <<! 2l <: i16) |.
    ((cast (bytes.[ sz 3 ] <: u8) <: i16) >>! 6l <: i16)
  in
  let r4:i16 =
    (((cast (bytes.[ sz 6 ] <: u8) <: i16) &. 3s <: i16) <<! 8l <: i16) |.
    ((cast (bytes.[ sz 5 ] <: u8) <: i16) &. 255s <: i16)
  in
  let r5:i16 =
    (((cast (bytes.[ sz 7 ] <: u8) <: i16) &. 15s <: i16) <<! 6l <: i16) |.
    ((cast (bytes.[ sz 6 ] <: u8) <: i16) >>! 2l <: i16)
  in
  let r6:i16 =
    (((cast (bytes.[ sz 8 ] <: u8) <: i16) &. 63s <: i16) <<! 4l <: i16) |.
    ((cast (bytes.[ sz 7 ] <: u8) <: i16) >>! 4l <: i16)
  in
  let r7:i16 =
    ((cast (bytes.[ sz 9 ] <: u8) <: i16) <<! 2l <: i16) |.
    ((cast (bytes.[ sz 8 ] <: u8) <: i16) >>! 6l <: i16)
  in
  let result:(i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16) =
    r0, r1, r2, r3, r4, r5, r6, r7 <: (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)
  in
  result
let split_forall_nat
  (#upper_bound: pos)
  (p: (i:nat{i <= upper_bound}) -> Type0)
  : Lemma (requires (if upper_bound = 0 then True else (forall (i:nat{i <= upper_bound - 1}). p i))
                   /\ p upper_bound
          )
          (ensures forall (i:nat{i <= upper_bound}). p i)
  = ()
#pop-options

// #push-options "--z3rlimit 60"
let rw_bit_or (b1 b2: bit) result:
  Lemma
    (requires (
        (b1 = 0 ==> b2 = 0 ==> result = 0)
      /\ (b1 = 0 ==> b2 = 1 ==> result = 1)
      /\ (b1 = 1 ==> b2 = 0 ==> result = 1)
      /\ (b1 = 1 ==> b2 = 1 ==> result = 0)
    ))
    (ensures (bit_or b1 b2 == result))
    = ()

let deserialize_10_int' (bytes: t_Array u8 (sz 10)): t_Array i16 (sz 8)
    = MkSeq.create8 (deserialize_10_int bytes)

exception StopCompute
let compute'' (): Tac unit
    = lset "goal" (cur_goal ());
      let _ = repeat (fun () -> 
          dump "A";
          norm [ iota; zeta; reify_
               ; delta_namespace ["FStar"; "RwLemmas"; "MkSeq"]
               ; primops; unmeta];
          dump "B";
          norm_pow2 ();
          dump "C";
          Tactics.Seq.norm_list_index ();
          norm_machine_int ();
          Tactics.Seq.simplify_index_seq_of_list ();
          dump "E";
          
          let goal0 = lget "goal" in
          let goal1 = cur_goal () in
          if term_eq goal0 goal1 then raise StopCompute;
          lset "goal" goal1
      ) in ()


let rw_get_bit_and (x y: int_t 't) i
  : Lemma (get_bit (x &. y) i == (if get_bit x i = 0 then 0 else get_bit y i))
    [SMTPat (get_bit (x &. y) i)]
  = get_bit_and x y i
  
let rw_get_bit_and_left (x y: int_t 't) i
  : Lemma (requires get_bit x i == 0) 
          (ensures get_bit (x &. y) i == 0)
          [SMTPat (get_bit (x &. y) i)]
  = get_bit_and x y i
let rw_get_bit_and_right (x y: int_t 't) i
  : Lemma (requires get_bit x i == 0) 
          (ensures get_bit (y &. x) i == 0)
          [SMTPat (get_bit (y &. x) i)]
  = get_bit_and x y i
let rw_get_bit_or_left (x y: int_t 't) i
  : Lemma (requires get_bit x i == 0)
          (ensures get_bit (x |. y) i == get_bit y i)
          [SMTPat (get_bit (x |. y) i)]
  = get_bit_or x y i
let rw_get_bit_or_right (x y: int_t 't) i
  : Lemma (requires get_bit y i == 0)
          (ensures get_bit (x |. y) i == get_bit x i)
          [SMTPat (get_bit (x |. y) i)]
  = get_bit_or x y i

let expect_get_bit t: Tac (option (term & term)) =
  let?# (f, [_typ; bit_value, _; i, _]) = expect_app_n t 3 in
  let?# () = expect_free_var f (`%get_bit) in
  Some (bit_value, i)

let expect_logand t: Tac (option (term & term)) =
  let?# (f, [_typ; x, _; y, _]) = expect_app_n t 3 in
  let?# () = expect_free_var f (`%logand) in
  Some (x, y)

let _simplify_via_mask () =
  let?# (t, _) = expect_lhs_eq_uvar () in
  let?# (bit_expr, i) = expect_get_bit t in
  let?# (x, y) = expect_logand bit_expr in
  let?# y = Tactics.MachineInts.term_to_machine_int_term y in
  let?# y = 
    let open Tactics.MachineInts in
    match y with
    | Op {op = MkInt; contents = Term contents} -> Some contents
    | _ -> None
  in
  let?# y = expect_pow2_minus_one_literal y in
  Some ()

let simplify_via_mask ()
  = rewrite_pow2_minus_one ();
    pointwise (fun _ ->
      match _simplify_via_mask () with
      | Some () -> ()
      | _ -> trefl ()
    )


let pow2_in_range t (n: nat {n < bits t - (if unsigned t then 0 else 1)})
    : Lemma (Rust_primitives.Integers.range (pow2 n - 1) t)
      [SMTPat (Rust_primitives.Integers.range (pow2 n - 1) t)]
    = Math.Lemmas.pow2_le_compat (bits t - (if unsigned t then 0 else 1)) n

// let _ = op_Bar_Dot

noeq type bit_expr =
  | Term: term -> bit_expr
  | Int: int -> bit_expr
  | And: x:bit_expr -> y:bit_expr -> bit_expr
  | Or: x:bit_expr -> y:bit_expr -> bit_expr
  | Shl: x:bit_expr -> shift:int -> bit_expr
  | Shr: x:bit_expr -> shift:int -> bit_expr
  | Cast: x:bit_expr -> bit_expr

let rec term_eq'' a b (n: nat): Tot _ (decreases n) =
  let open FStar.Stubs.Reflection.V2.Data in
  if n = 0 then term_eq a b else
  match (inspect_ln a, inspect_ln b) with
  | (Tv_FVar a, Tv_FVar b)
  | (Tv_FVar a, Tv_UInst b _)
  | (Tv_UInst a _, Tv_FVar b)
  | (Tv_UInst a _, Tv_UInst b _) -> inspect_fv a = inspect_fv b
  | (Tv_Var _, Tv_Var _) -> term_eq a b
  | (Tv_App _ _, Tv_App _ _) ->
    let a, a_args = collect_app_ln a in
    let b, b_args = collect_app_ln b in
    let a_args = L.filter (fun (_, x) -> Q_Explicit? x) a_args in
    let b_args = L.filter (fun (_, x) -> Q_Explicit? x) b_args in
    L.length a_args = L.length b_args
    && (
    let rec h a_args (b_args: _ {L.length a_args == L.length b_args}) =
      match a_args, b_args with
      | ((ahd,_)::atl), ((bhd,_)::btl) -> 
        term_eq'' ahd bhd (n - 1) && h atl btl
      | [], [] -> true
    in h a_args b_args
    )
  | (Tv_AscribedT a _ _ _, _)
  | (Tv_AscribedC a _ _ _, _) -> term_eq'' a b (n-1)
  | (_, Tv_AscribedT b _ _ _)
  | (_, Tv_AscribedC b _ _ _) -> term_eq'' a b (n-1)
  | (Tv_Type _, Tv_Type _) -> true
  | (Tv_Refine _ a, _) -> term_eq'' a b (n - 1)
  | (_, Tv_Refine _ b) -> term_eq'' a b (n - 1)
    // && term_eq' a b && L.fold_left (fun i a -> L.index b_args i `term_eq'` a)
  // | Tv_Var    : v:namedv -> named_term_view
  // | Tv_BVar   : v:bv -> named_term_view
  // | Tv_FVar   : v:fv -> named_term_view
  // | Tv_UInst  : v:fv -> us:universes -> named_term_view
  // | Tv_App    : hd:term -> a:argv -> named_term_view
  // | Tv_Abs    : b:binder -> body:term -> named_term_view
  // | Tv_Arrow  : b:binder -> c:comp -> named_term_view
  // | Tv_Type   : universe -> named_term_view
  // | Tv_Refine : b:simple_binder -> ref:term -> named_term_view
  // | Tv_Const  : vconst -> named_term_view
  // | Tv_Uvar   : nat -> ctx_uvar_and_subst -> named_term_view
  // | Tv_Let    : recf:bool -> attrs:(list term) -> b:simple_binder -> def:term -> body:term -> named_term_view
  // | Tv_Match  : scrutinee:term -> ret:option match_returns_ascription -> brs:(list branch) -> named_term_view
  // | Tv_AscribedT : e:term -> t:term -> tac:option term -> use_eq:bool -> named_term_view
  // | Tv_AscribedC : e:term -> c:comp -> tac:option term -> use_eq:bool -> named_term_view
  // | Tv_Unknown  : named_term_view // An underscore: _
  // | Tv_Unsupp : named_term_view // failed to inspect, not supported
  | _ -> term_eq a b

let term_eq' a b = term_eq'' a b 99999

let rec bit_expr_eq a b =
  match (a, b) with
  | Term a, Term b -> term_eq' a b
  | Int a, Int b -> a = b
  | And xa ya, And xb yb
  | Or  xa ya, Or  xb yb -> bit_expr_eq xa xb && bit_expr_eq ya yb
  | Shl  a sa, Shl  b sb
  | Shr  a sa, Shr  b sb -> bit_expr_eq  a  b && sa = sb
  | Cast    a, Cast    b -> bit_expr_eq  a  b
  | _ -> false

let rec bit_expr_contains needle haystack =
  let recurse = bit_expr_contains needle in
  bit_expr_eq needle haystack
  || ( match haystack with
    | And l r | Or l r -> recurse l || recurse r
    | Cast x | Shl x _ | Shr x _ -> recurse x
    | _ -> false)

let expect_machine_int_lit t: Tac _ =
  let open Tactics.MachineInts in
  let?# expr = term_to_machine_int_term t in
  match expr with
  | Op {op = MkInt; contents = Lit n} -> Some n
  | _ -> None

let rec term_to_bit_expr' t: Tac _
  = match expect_machine_int_lit t with
  | Some n -> Int n
  | _ -> match let?# (f, args) = collect_app_hd t in
              let?# (x, y) = match args with
                             | [_; x,_; y,_] | [_; _; x,_; y,_]
                             | [_; _; _; x,_; y,_] -> Some (x, y) | _ -> None in
              match f with
              | `%logand      | `%( &.  ) 
                  -> Some (And (term_to_bit_expr' x) (term_to_bit_expr' y))
              | `%logor       | `%( |.  ) 
                  -> Some (Or  (term_to_bit_expr' x) (term_to_bit_expr' y))
              | `%shift_left  | `%( <<! ) 
                  -> let?# y = expect_machine_int_lit y in
                    Some (Shl (term_to_bit_expr' x) y)
              | `%shift_right | `%( >>! ) 
                  -> let?# y = expect_machine_int_lit y in
                    Some (Shr (term_to_bit_expr' x) y)
              | `%cast -> Some (Cast (term_to_bit_expr' y))
              | _ -> None
        with
        | Some t -> t
        | None   -> Term t

let term_to_bit_expr t: Tac (option (x: bit_expr {~(Term? x)}))
  = match term_to_bit_expr' t with
  | Term _ -> None
  | t -> Some t

let expect_get_bit_expr t: Tac _
  = let?# (expr, index) = expect_get_bit t in
    let?# index = expect_machine_int_lit index in
    let expr = term_to_bit_expr' expr in
    Some (expr, index)


let op_Bar_GreaterThan (x: 'a) (f: 'a -> Tac 'b): Tac 'b = f x

let get_bit_shl_zero #t #u (x: int_t t) (y: int_t u) (i: usize {v i < bits t})
  : Lemma (requires v y >= 0 /\ v y < bits t /\ v i < v y)
          (ensures get_bit (x <<! y) i == 0)
    = get_bit_shl x y i

let get_bit_shr_zero #t #u (x: int_t t) (y: int_t u) (i: usize {v i < bits t})
  : Lemma (requires v y >= 0 /\ v y < bits t /\ (v i >= bits t - v y /\ (if signed t then (get_bit x (mk_int (bits t - 1)) == 0) else true)))
          (ensures get_bit (x >>! y) i == 0)
    = get_bit_shr x y i

let get_bit_shl_one #t #u (x: int_t t) (y: int_t u) (i: usize {v i < bits t})
  : Lemma (requires v y >= 0 /\ v y < bits t /\ v i >= v y)
          (ensures get_bit (x <<! y) i == get_bit x (mk_int (v i - v y)))
    [SMTPat (get_bit (x <<! y) i)] = get_bit_shl x y i

let get_bit_shr #t #u (x: int_t t) (y: int_t u {v y >= 0 /\ v y < bits t}) (i: usize {v i < bits t})
  : Lemma (ensures get_bit (shift_right x y) i 
               == 1)
                // == (if v i < bits t - v y
                //     then get_bit x (mk_int (v i + v y))
                //     else if signed t
                //          then get_bit x (mk_int (bits t - 1))
                //          else 0))
          // (ensures get_bit (x >>! y) i 
          //       == (if v i < bits t - v y
          //           then get_bit x (mk_int (v i + v y))
          //           else if signed t
          //                then get_bit x (mk_int (bits t - 1))
          //                else 0))
    [SMTPat (get_bit (x >>! y) i)]
    = admit ()

/// Proves that `get_bit .. ..` is zero
let rec solve_get_bit_zero (): Tac _ =
  let (lhs, rhs, _) = expect_lhs_eq_rhs () |> expect "a goal `<lhs> == <rhs>` (solve_get_bit_zero)" in
  print ("solve_get_bit_zero: " ^ term_to_string lhs);
  let (lhs, i) = expect_get_bit_expr lhs |> expect "LHS to be `get_bit .. ..`" in
  let rhs' = expect_int_literal rhs |> expect ("RHS to be a int literal, got " ^ term_to_string rhs) in
  let _ = match rhs' with | 0 -> () | _ -> fail "RHS should be zero" in
  match lhs with
  | Term _ -> fail ("LHS is an arbitrary term, I cannot prove it is " ^ string_of_int rhs')
  | Int _ -> (compute (); trefl ())
  | Shl _ _ -> 
    let _ = rewrite_lhs () in
    flip ();
    apply_lemma_rw (`get_bit_shl);
    (fun _ -> 
    norm_machine_int (); compute (); norm [simplify];
    trivial () )`or_else` (fun _ -> fail' "Shl: tried to prove it was zero")
  | Shr _ _ -> 
    let _ = rewrite_lhs () in
    flip ();
    apply_lemma_rw_eqtype (`get_bit_shr);
    focus (fun _ -> 
      let _ = repeat split in
      iterAll (fun _ -> 
          match expect_lhs_eq_rhs () with
          | Some _ -> print "solve_get_bit_zero: recurse";
                     solve_get_bit_zero ()
          | _ -> (fun _ -> norm_machine_int (); 
                compute (); 
                norm [simplify];
                trivial ()) `or_else` (fun _ -> fail' "Shr: tried to prove it was zero")
      )
    )
  | Cast _ -> 
     (try
        if rhs' = 0 then apply_lemma (`get_bit_cast_extend) else ();
        compute (); norm [simplify];
        trivial `or_else` (fun _ -> fail' "Cast: tried to prove it was zero")
      with | _ -> (
        apply_lemma (`get_bit_cast);
        compute (); norm [simplify];
        trivial `or_else` (fun _ -> fail' "Cast: tried to prove it was zero [second path]")
     ))
  | And x y -> fail "And: unsupported"
  | _ -> fail "unsupported"


let rw_get_bit_and_one_right (x y: int_t 't) i
  : Lemma (requires get_bit x i == 1) 
          (ensures get_bit (y &. x) i == get_bit y i)
  = get_bit_and x y i

let _solve_get_bit_equality lhs i rhs j: Tac _ =
  match lhs with
  | Term x -> trefl `or_else` (fun _ -> fail' "solve_get_bit_equality: expected terms to be equal at this point")
  | And x y -> 
         let _ = rewrite_lhs () in
         flip ();
         apply_lemma_rw (`rw_get_bit_and_one_right);
         fail "xxx";
         ()
  | Or x y -> 
         print ("We are looking at `x |. y`");
         print ("x=" ^ term_to_string (quote x));
         print ("y=" ^ term_to_string (quote y));
         print ("RHS=" ^ term_to_string (quote rhs));
        (match bit_expr_contains rhs x, bit_expr_contains rhs y with
        | false, false -> 
          fail' "RHS was expected to be on the LHS or RHS of the logor!"
        | true, true -> fail' "RHS was expected to be on the LHS or RHS of the logor, not both!"
        | true, false -> 
          let rw = rewrite_lhs () in
          flip ();
          dump' "solve_get_bit_equality: LEFT (BEFORE)";
          apply_lemma_rw (norm_term [] (`rw_get_bit_or_right));
          dump' "solve_get_bit_equality: LEFT (AFTE RLEMMA)";
          print "solve_get_bit_equality: LEFT";
          solve_get_bit_zero ()
        | false, true -> 
          let rw = rewrite_lhs () in
          flip ();
          print "solve_get_bit_equality: RIGHT";
          apply_lemma_rw (norm_term [] (`rw_get_bit_or_left));
          solve_get_bit_zero ()
        )
  | _ -> fail' "xxxpppppp"

let swap_eq2_goal p q: Lemma (requires eq2 p q) (ensures eq2 q p) = ()

let rec solve_get_bit_equality' can_invert: Tac _ =
  let (lhs, rhs, _) = expect_lhs_eq_rhs () |> expect "a goal `<lhs> == <rhs>`" in
  print ("solve_get_bit_equality: (" ^ term_to_string lhs ^ ") == (" ^ term_to_string rhs ^ ")");
  let (lhs, i) = expect_get_bit_expr lhs |> expect "LHS to be `get_bit .. ..`" in
  let (rhs, j) = expect_get_bit_expr rhs |> expect "RHS to be `get_bit .. ..`" in
  if bit_expr_contains rhs lhs |> not 
  then if can_invert
       then (apply_lemma (`swap_eq2_goal); solve_get_bit_equality' false)
       else fail "was expected the bit expression on RHS to be included in the one of LHS"
  else _solve_get_bit_equality lhs i rhs j
let solve_get_bit_equality (): Tac _ =
  solve_get_bit_equality' true

let rec term_to_string'' (t: term): Tac string
  = match t with
  | Tv_App f (x, Q_Meta _) -> term_to_string'' f
  | Tv_App f (x, aqualv) ->
    let qual = match aqualv with | Q_Implicit -> "#" | Q_Explicit -> "" in
    term_to_string' f ^ " " ^ qual ^ "(" ^ term_to_string' x ^ ")"
  | Tv_UInst v _ | Tv_FVar v -> 
      let v = implode_qn (inspect_fv v) in
      (match v with
      | `%get_bit -> "get_bit"
      | `%bit -> "bit"
      | `%eq2 -> "eq2"
      | `%u8 -> "u8"
      | `%u16 -> "u16"
      | `%i16 -> "i16"
      | `%i32 -> "i32"
      | `%sz -> "sz"
      | `%usize -> "usize"
      | _ -> v
      )
  | _ -> term_to_string t
and term_to_string' t: Tac _ =  term_to_string'' t

// get_bit (Seq.Base.index bytes 2) (sz 1) ==
// get_bit ((cast bytes.[ sz 2 ] &. 15s) <<! 6l |. cast bytes.[ sz 1 ] >>! 2l) (sz 7)

let opts = "--using_facts_from '-* +Rust_primitives.BitVectors
+Rust_primitives.Integers.get_bit_cast +Rust_primitives.Integers.get_bit_and +Rust_primitives.Integers.get_bit_or +Rust_primitives.Integers.get_bit_shl +Rust_primitives.Integers.get_bit_shr +Rust_primitives.Integers.get_bit_cast_extend'"

#push-options "--z3rlimit 80"
let fff_ bytes x: unit = 
    let bv1 = bit_vec_of_int_t_array bytes 8 in
    let out = deserialize_10_int' bytes in
    let bv2 = bit_vec_of_int_t_array out 10 in
    let i = 77 in
    if false then
    assert (bv1 i == bv2 i) by (
      norm [
        iota; primops; 
        delta_only [`%bit_vec_of_int_t_array; `%FunctionalExtensionality.on];
      ];
      compute'' ();
      set_options opts;
      dump "SMT NOW";
      smt_sync ();
      // squash_intro ();
      // print (term_to_string' (cur_goal()));
      fail "DONE"
    )
#pop-options

#push-options "--compat_pre_core 0"
#push-options "--z3rlimit 80"
#push-options "--print_implicits"
let asdsd (bytes: t_Array u8 (sz 10))
    = let cast: u8 -> i16 = cast in
      assert (
        eq2 #(bit) (get_bit #(Lib.IntTypes.U8) (FStar.Seq.Base.index #(Rust_primitives.Integers.int_t (Lib.IntTypes.U8)) (bytes) (2)) (sz (1))) (get_bit #(Lib.IntTypes.S16) (Rust_primitives.Integers.op_Bar_Dot #(Lib.IntTypes.S16) (Rust_primitives.Integers.op_Less_Less_Bang #(Lib.IntTypes.S16) #(Lib.IntTypes.S32) (Rust_primitives.Integers.op_Amp_Dot #(Lib.IntTypes.S16) (Rust_primitives.cast #(u8) #(i16) #(Rust_primitives.cast_tc_integers (Lib.IntTypes.U8) (Lib.IntTypes.S16)) (Core.Ops.op_String_Access #(Rust_primitives.Arrays.t_Array (u8) (sz (10))) #(usize) #(Rust_primitives.Hax.impl__index (u8) (sz (10)) (Rust_primitives.Integers.usize_inttype)) (bytes) (sz (2)))) (FStar.Int16.int_to_t (15))) (FStar.Int32.int_to_t (6))) (Rust_primitives.Integers.op_Greater_Greater_Bang #(Lib.IntTypes.S16) #(Lib.IntTypes.S32) (Rust_primitives.cast #(u8) #(i16) #(Rust_primitives.cast_tc_integers (Lib.IntTypes.U8) (Lib.IntTypes.S16)) (Core.Ops.op_String_Access #(Rust_primitives.Arrays.t_Array (u8) (sz (10))) #(usize) #(Rust_primitives.Hax.impl__index (u8) (sz (10)) (Rust_primitives.Integers.usize_inttype)) (bytes) (sz (1)))) (FStar.Int32.int_to_t (2)))) (sz (7)))
         // get_bit (
         //      ((cast bytes.[ sz 3 ] <: i16) &. 63s <: i16) <<! 4l 
         //   |. (cast bytes.[ sz 2 ] <: i16) >>! 4l
         // ) (sz 5)
         // == get_bit (cast bytes.[ sz 3 ] <: i16) (sz 0)
      ) by (
        norm [iota; delta_only [`%( .[] ); `%Core.Ops.Index.Mkt_Index; `%Rust_primitives.Hax.impl__index; `%Core.Ops.Index.f_index]];
        Tactics.MachineInts.(transform norm_generic_machine_int_term);
        solve_get_bit_equality ();
        // print (term_to_string' (cur_goal()));
        // smt_sync ();
        fail "done"
      )





let fff bytes x: unit = 
    assert (
          get_bit (Seq.index (deserialize_10_int' bytes) 0) (sz 3) 
       == get_bit (Seq.index bytes 0) (sz 3)
    ) by (
      compute'' ();
      smt_sync ();
      // l_to_r [`rewrite_to_zero];
      // compute'' ();
      // apply_lemma_rw 
      // l_to_r [`rw_rhs_bit_or_no_mask];
      fail "DONE";
      focus (tadmit)
    );
    ()






#push-options "--z3rlimit 80"
let rw_rhs_bit_or #t #u #shift_t
    (lhs: int_t u) (rhs: int_t t) 
    (relevant_bits: nat {relevant_bits < bits t - (if unsigned t then 0 else 1)})
    (i: nat {i < bits u})
    (shift: nat {shift < bits u /\ Rust_primitives.Integers.range shift shift_t})
    : Lemma (
         let full = get_bit (
             lhs |. 
             ((cast (rhs &. mk_int (pow2 relevant_bits - 1)) <: int_t u) <<! mk_int #shift_t shift)
         ) (sz i) in
         full == (if i >= relevant_bits + shift || i < shift then get_bit lhs (sz i) else full)
      )
    = if i >= relevant_bits + shift then (
           let i' = i - shift in
           let mask: int_t t = mk_int (pow2 relevant_bits - 1) in
           let a = rhs &. mask in
           if i' < bits t then (
             get_bit_pow2_minus_one #t relevant_bits (sz i');
             get_bit_and rhs (mk_int (pow2 relevant_bits - 1)) (sz i')
           ) else get_bit_cast_extend #t #u a (sz i');
           let a: int_t u = cast a in
           get_bit_shl #u #shift_t a (mk_int shift) (sz i')
      ) else if i < shift then () else ()
#pop-options

#push-options "--z3rlimit 80"
let rw_rhs_bit_or_no_mask #t #u #shift_t
    (lhs: int_t u) (rhs: int_t t) 
    (i: nat {i < bits u})
    (shift: nat {shift < bits u /\ Rust_primitives.Integers.range shift shift_t})
    : Lemma (
         let full = get_bit (
             lhs |. ((cast rhs <: int_t u) <<! mk_int #shift_t shift)
         ) (sz i) in
         full == (if i < shift then get_bit lhs (sz i) else full)
      )
    = if i >= shift then (
           let i' = i - shift in
           let a = rhs in
           let a: int_t u = cast a in
           get_bit_shl #u #shift_t a (mk_int shift) (sz i')
      ) else ()
#pop-options

#push-options "--z3rlimit 150"
let add_shift_zero #t #shift_t (x: int_t t)
    : Lemma (x <<! mk_int #shift_t 0 == x)
    = assert (x <<! mk_int #shift_t 0 == x) by (compute ())
#pop-options


let add_shift_zero_specific #t #u #shift_t
    (lhs: int_t u) (rhs: int_t t) 
    (relevant_bits: nat {relevant_bits < bits t - (if unsigned t then 0 else 1)})
    (i: nat {i < bits u})
    : Lemma (
            (cast (rhs &. mk_int (pow2 relevant_bits - 1)) <: int_t u)
         == ((cast (rhs &. mk_int (pow2 relevant_bits - 1)) <: int_t u) <<! mk_int #shift_t 0)
       )
    = add_shift_zero #u #shift_t (cast (rhs &. mk_int (pow2 relevant_bits - 1)) <: int_t u)

