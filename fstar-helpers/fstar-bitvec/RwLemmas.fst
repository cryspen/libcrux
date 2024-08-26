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
  = get_bit_and x y i
let rw_get_bit_and_right (x y: int_t 't) i
  : Lemma (requires get_bit x i == 0) 
          (ensures get_bit (y &. x) i == 0)
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

exception Restore
let dump' (msg: string): Tac unit
    = try let _ = repeat clear_top in set_smt_goals []; dump msg with | _ -> ()

// let _ = op_Bar_Dot

noeq type bit_expr =
  | Term: term -> bit_expr
  | Int: int -> bit_expr
  | And: x:bit_expr -> y:bit_expr -> bit_expr
  | Or: x:bit_expr -> y:bit_expr -> bit_expr
  | Shl: x:bit_expr -> shift:int -> bit_expr
  | Shr: x:bit_expr -> shift:int -> bit_expr
  | Cast: x:bit_expr -> bit_expr

let rec bit_expr_eq a b =
  match (a, b) with
  | Term a, Term b -> term_eq a b
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

let fail' msg = dump msg; fail msg

let expect (msg: string) (x: option 'a): Tac 'a
  = match x with
  | None -> 
    dump' ("Expected " ^ msg);
    fail ("Expected " ^ msg)
  | Some x -> x

let op_Bar_GreaterThan (x: 'a) (f: 'a -> Tac 'b): Tac 'b = f x

let get_bit_shl_zero #t #u (x: int_t t) (y: int_t u) (i: usize {v i < bits t})
  : Lemma (requires v y >= 0 /\ v y < bits t /\ v i < v y)
          (ensures get_bit (x <<! y) i == 0)
    = get_bit_shl x y i

let get_bit_shr_zero #t #u (x: int_t t) (y: int_t u) (i: usize {v i < bits t})
  : Lemma (requires v y >= 0 /\ v y < bits t /\ v i >= bits t - v y /\ (if signed t then (get_bit x (mk_int (bits t - 1)) == 0) else true))
          (ensures get_bit (x >>! y) i == 0)
    = get_bit_shr x y i

let get_bit_shl_one #t #u (x: int_t t) (y: int_t u) (i: usize {v i < bits t})
  : Lemma (requires v y >= 0 /\ v y < bits t /\ v i >= v y)
          (ensures get_bit (x <<! y) i == get_bit x (mk_int (v i - v y)))
    [SMTPat (get_bit (x <<! y) i)] = get_bit_shl x y i

let rewrite_lhs (): Tac _ =
  let (lhs, _, _) = expect_lhs_eq_rhs () |> expect "a goal `<lhs> == <rhs>` (rewrite_lhs)" in
  let uvar = fresh_uvar (Some (tc (cur_env ()) lhs)) in
  tcut (`squash (`#lhs == `#uvar))

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
    apply_lemma (`get_bit_shl_zero);
    (fun _ -> 
    norm_machine_int (); compute (); norm [simplify];
    trivial () )`or_else` (fun _ -> fail' "Shl: tried to prove it was zero")
  | Shr _ _ -> 
    apply_lemma (`get_bit_shr_zero);
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
          apply_lemma_rw (norm_term [] (`rw_get_bit_or_right));
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

let solve_get_bit_equality (): Tac _ =
  let (lhs, rhs, _) = expect_lhs_eq_rhs () |> expect "a goal `<lhs> == <rhs>`" in
  print ("solve_get_bit_equality: (" ^ term_to_string lhs ^ ") == (" ^ term_to_string rhs ^ ")");
  let (lhs, i) = expect_get_bit_expr lhs |> expect "LHS to be `get_bit .. ..`" in
  let (rhs, j) = expect_get_bit_expr rhs |> expect "RHS to be `get_bit .. ..`" in
  if bit_expr_contains rhs lhs |> not 
  then fail "was expected the bit expression on RHS to be included in the one of LHS";
  _solve_get_bit_equality lhs i rhs j;
  ()


#push-options "--compat_pre_core 0"
let asdsd (bytes: t_Array u8 (sz 10))
    = let cast: u8 -> i16 = cast in
      assert (
         get_bit (
              ((cast bytes.[ sz 3 ] <: i16) &. 63s <: i16) <<! 4l 
           |. (cast bytes.[ sz 2 ] <: i16) >>! 4l
         ) (sz 5)
         == get_bit (cast bytes.[ sz 3 ] <: i16) (sz 0)
      ) by (
        Tactics.MachineInts.(transform norm_generic_machine_int_term);
        solve_get_bit_equality ();
        // dump "XXXX";
        // simplify_via_mask ();
        // fail "-------";
        // pointwise' (fun _ -> 
        //    let _ = let?# (t, _) = expect_lhs_eq_uvar () in
                   
        //            let?# (f, _) = expect_app_n t 3 in
        //            let?# () = expect_free_var f (`%get_bit) in
        //            // norm [ iota; zeta; reify_
        //            //      ; primops; unmeta];
        //            dump' "xxxxx";
        //            // apply_lemma_rw (`(rw_rhs_bit_or_no_mask #Lib.IntTypes.U8 #Lib.IntTypes.S16 #Lib.IntTypes.S32 ((`@cast) (`@bytes).[ sz 3 ] &. 63s <: i16)));
        //            // invert ();
        //            Some ()
        //    in
        //    trefl ()
        //    // let _ = repeat clear_top in
        //    // dump "X";
        //    // (fun _ -> apply_lemma_rw (`rw_rhs_bit_or_no_mask)) `or_else` trefl;
        //    // let _ = repeat clear_top in
        //    // dump "Y"
        // );
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

