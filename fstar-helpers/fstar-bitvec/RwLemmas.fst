module RwLemmas

open Core
module L = FStar.List.Tot
open FStar.Tactics.V2
open FStar.Tactics.V2.SyntaxHelpers
open FStar.Class.Printable
open FStar.Mul

let rw_seq_index_list #t (l: list t) i
    : Lemma (Seq.Base.index (Seq.Base.seq_of_list l) i == FStar.List.Tot.index l i) 
    = ()

// START TEMPLATE
let rw_u8_mk_int x: Lemma (mk_int #u8_inttype x == UInt8.uint_to_t x) = mk_int_equiv_lemma #u8_inttype x
let rw_u8_v_int_to x: Lemma (UInt8.v (UInt8.uint_to_t x) == x) = ()
let rw_u8_int_to_v x: Lemma (UInt8.uint_to_t (UInt8.v x) == x) = ()
let rw_u8_v x: Lemma (v #u8_inttype x == UInt8.v x) = ()
// END TEMPLATE

// START GENERATED
let rw_i8_mk_int x: Lemma (mk_int #i8_inttype x == Int8.int_to_t x) = mk_int_equiv_lemma #i8_inttype x
let rw_i8_v_int_to x: Lemma (Int8.v (Int8.int_to_t x) == x) = ()
let rw_i8_int_to_v x: Lemma (Int8.int_to_t (Int8.v x) == x) = ()
let rw_i8_v x: Lemma (v #i8_inttype x == Int8.v x) = ()
let rw_u16_mk_int x: Lemma (mk_int #u16_inttype x == UInt16.uint_to_t x) = mk_int_equiv_lemma #u16_inttype x
let rw_u16_v_int_to x: Lemma (UInt16.v (UInt16.uint_to_t x) == x) = ()
let rw_u16_int_to_v x: Lemma (UInt16.uint_to_t (UInt16.v x) == x) = ()
let rw_u16_v x: Lemma (v #u16_inttype x == UInt16.v x) = ()
let rw_i16_mk_int x: Lemma (mk_int #i16_inttype x == Int16.int_to_t x) = mk_int_equiv_lemma #i16_inttype x
let rw_i16_v_int_to x: Lemma (Int16.v (Int16.int_to_t x) == x) = ()
let rw_i16_int_to_v x: Lemma (Int16.int_to_t (Int16.v x) == x) = ()
let rw_i16_v x: Lemma (v #i16_inttype x == Int16.v x) = ()
let rw_u32_mk_int x: Lemma (mk_int #u32_inttype x == UInt32.uint_to_t x) = mk_int_equiv_lemma #u32_inttype x
let rw_u32_v_int_to x: Lemma (UInt32.v (UInt32.uint_to_t x) == x) = ()
let rw_u32_int_to_v x: Lemma (UInt32.uint_to_t (UInt32.v x) == x) = ()
let rw_u32_v x: Lemma (v #u32_inttype x == UInt32.v x) = ()
let rw_i32_mk_int x: Lemma (mk_int #i32_inttype x == Int32.int_to_t x) = mk_int_equiv_lemma #i32_inttype x
let rw_i32_v_int_to x: Lemma (Int32.v (Int32.int_to_t x) == x) = ()
let rw_i32_int_to_v x: Lemma (Int32.int_to_t (Int32.v x) == x) = ()
let rw_i32_v x: Lemma (v #i32_inttype x == Int32.v x) = ()
let rw_u64_mk_int x: Lemma (mk_int #u64_inttype x == UInt64.uint_to_t x) = mk_int_equiv_lemma #u64_inttype x
let rw_u64_v_int_to x: Lemma (UInt64.v (UInt64.uint_to_t x) == x) = ()
let rw_u64_int_to_v x: Lemma (UInt64.uint_to_t (UInt64.v x) == x) = ()
let rw_u64_v x: Lemma (v #u64_inttype x == UInt64.v x) = ()
let rw_i64_mk_int x: Lemma (mk_int #i64_inttype x == Int64.int_to_t x) = mk_int_equiv_lemma #i64_inttype x
let rw_i64_v_int_to x: Lemma (Int64.v (Int64.int_to_t x) == x) = ()
let rw_i64_int_to_v x: Lemma (Int64.int_to_t (Int64.v x) == x) = ()
let rw_i64_v x: Lemma (v #i64_inttype x == Int64.v x) = ()
let rw_integers_list0 = [
     `rw_u8_mk_int;`rw_u8_v_int_to;`rw_u8_int_to_v;`rw_u8_v
    // ;`rw_i8_mk_int;`rw_i8_v_int_to;`rw_i8_int_to_v;`rw_i8_v;`rw_u16_mk_int;`rw_u16_v_int_to;`rw_u16_int_to_v;`rw_u16_v
    ;`rw_i16_mk_int;`rw_i16_v_int_to;`rw_i16_int_to_v;`rw_i16_v
    // ;`rw_u32_mk_int;`rw_u32_v_int_to;`rw_u32_int_to_v;`rw_u32_v;`rw_i32_mk_int;`rw_i32_v_int_to;`rw_i32_int_to_v;`rw_i32_v;`rw_u64_mk_int;`rw_u64_v_int_to;`rw_u64_int_to_v;`rw_u64_v;`rw_i64_mk_int;`rw_i64_v_int_to;`rw_i64_int_to_v;`rw_i64_v
    ]
// END GENERATED

let rw_generic_v_mk_int t (x: int {Rust_primitives.Integers.range x t})
  : Lemma (v (mk_int #t x) == x)
  = ()
let rw_usize_v_mk_int x: Lemma (v #usize_inttype (mk_int #usize_inttype x) == x) = ()
let rw_v_mk_int_usize x: Lemma (mk_int #usize_inttype (v #usize_inttype x) == x) = ()

let rw_integers_list = L.append rw_integers_list0 [
  `rw_generic_v_mk_int;
  `rw_usize_v_mk_int;
  `rw_v_mk_int_usize;
]

let (let?#) (x: option 'a) (f: 'a -> Tac (option 'b)): Tac (option 'b)
  = match x with
  | Some x -> f x
  | None   -> None

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
let expect_cur_formula_comp () = 
    match FStar.Tactics.V2.Logic.cur_formula () with
    | Comp _ lhs _ -> Some lhs
    | _ -> None
let expect_app_n t n: Tac (option (term & (l: list _ {L.length l == n}))) =
    let (head, args) = collect_app t in
    if L.length args = n
    then Some (head, args)
    else None

exception DoRefl
let fast_l_to_r_integers (): Tac unit =
  pointwise (fun () -> 
      try
      match let?# t = expect_cur_formula_comp () in
            let (f, args) = collect_app t in
            let?# _ = if Cons? args then Some () else None in
            let?# fv = expect_fvar f in
            let fv = explode_qn fv in
            if Cons? fv then
              (match L.last fv with
              | "v" | "mk_int" | "int_to_t" | "uint_to_t"
                -> fold_left (fun k l () -> (fun () -> apply_lemma_rw l) `or_else` k)
                              trefl rw_integers_list ()
              | _ -> raise DoRefl
              ) else raise DoRefl;
            Some () 
      with None -> raise DoRefl | _ -> ()
      with | DoRefl -> trefl ()
           | e -> raise e
    )

#push-options "--compat_pre_core 0"

let expect_pow2_literal t: Tac (option int)
    = let?# (f, [x, _]) = expect_app_n t 1 in
      let?# () = expect_free_var f (`%pow2) in
      expect_int_literal x

/// Fully normalize a term of the shape `pow2 n`, where `n` is a literal
let norm_pow2 (): Tac unit =
  pointwise (fun () -> 
    let _ = let?# t = expect_cur_formula_comp () in
            let?# n = expect_pow2_literal t in
            debug ("Normalized `pow2 " ^ string_of_int n ^ "`");
            Some (norm [iota; zeta_full; reify_; delta; primops; unmeta]) in
    trefl ())

let rec log2 (n: nat): Tot (option (m: nat {pow2 m == n})) (decreases n)
    = if n = 0 then None
      else if n = 1 then Some 0
      else if n % 2 <> 0 then None
           else match log2 (n / 2) with
                | Some n -> Some (1 + n)
                | None   -> None

let lemma_of_refinement #t #p (n: t {p n}): Lemma (p n) = ()

let rewrite_pow2_minus_one () =
   pointwise (fun () -> 
    match let?# t = expect_cur_formula_comp () in
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

let _ = fun (i: nat) -> assert (pow2 (i + 3) + pow2 10 == pow2 (i + 3) + 1024)
                       by (norm_pow2 (); trefl ())

private 
let unfold_index_lemma (#a: Type) (l: list a) (i:nat{i < List.Tot.length l})
  : Lemma (  FStar.List.Tot.index #a l i 
          == Pervasives.norm [iota; primops] (let hd::tl = l in
    if i = 0 then hd else List.Tot.index tl (i - 1)))
  = ()


let rec repeatWhile (f: unit -> Tac bool): Tac unit
  = if f () then repeatWhile f

exception StopNormIndex
let norm_index (): Tac unit =
  let _ = repeat (fun _ ->
    lset "found" false;
    pointwise (fun _ ->
      (fun () ->
         match let?# t = expect_cur_formula_comp () in
               let?# (f, [typ, _; l, _; index, _]) = expect_app_n t 3 in
               let?# () = expect_free_var f (`%FStar.List.Tot.index) in
               let?# n = expect_int_literal index in
               apply_lemma_rw (`unfold_index_lemma);
               lset "found" true;
               Some ()
         with | Some () -> () | _ -> raise DoRefl
      ) `or_else` trefl);
    if lget "found" then () else raise StopNormIndex) in ()

let _ = assert (L.index [1;2;3;4;5;6] 3 == 4) by (norm_index(); trefl ())

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
               // ; delta_only [
               //              `%( +! ); `%( -! ); `%( *! ); `%( /! );
               //              `%add; `%mul; `%div; `%sub
               //   ]
               ; primops; unmeta];
          dump "B";
          norm_pow2 ();
          dump "C";
          l_to_r [`rw_seq_index_list];
          fast_l_to_r_integers ();
          dump "D";
          norm_index ();
          dump "E";
          
          let goal0 = lget "goal" in
          let goal1 = cur_goal () in
          if term_eq goal0 goal1 then raise StopCompute;
          lset "goal" goal1
      ) in ()

// (((cast (bytes.[ sz 2 ] <: u8) <: i16) &. 15s <: i16) <<! 6l <: i16) |.
//     ((cast (bytes.[ sz 1 ] <: u8) <: i16) >>! 2l <: i16)

// let _ = assert ((4s +! 5s) <<! 3s == 3s) by (
//       compute'' ();
//       fail "x"
    // )

// let ( << ) (#t:inttype) (a:int_t t) (b:nat {b >= 0 /\ b < bits t}) =
//     let x:range_t t = (v a * pow2 b) @%. t in
//     mk_int #t x

// let rw_shift_left_to_nat
//     #t #u (x: int_t t) (y: int_t u {v y >= 0 /\ v y < bits t})
//     : Lemma ((x <<! y) == (x <<! (mk_int #t (v y)) <: int_t t)) = ()

// let rw_get_bit_add_or #t #u #shift (x: int_t t) (shift: int_t shift)
//     : Lemma (get_bit (cast (x &. mask) <<! shift))
    

// let f #t (x: int_t t)
//     // (x y: int_t t)
//     // ()


// let _ = get_bit (
//     (  cast bytes.[ sz 3 ] &. 63s) <<! 4l 
//     |. cast bytes.[ sz 2 ] >>! 4l
//     ) (sz 3) == 0

// let _ =
//     get_bit (  ((cast bytes.[ sz 1 ] &. 3s  ) <<! 8l)
//              |. cast bytes.[ sz 0 ] &. 255s
//             ) (sz 3) == 0


let pow2_in_range t (n: nat {n < bits t - (if unsigned t then 0 else 1)})
    : Lemma (Rust_primitives.Integers.range (pow2 n - 1) t)
      [SMTPat (Rust_primitives.Integers.range (pow2 n - 1) t)]
    = Math.Lemmas.pow2_le_compat (bits t - (if unsigned t then 0 else 1)) n


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

// let goal (bytes: t_Array u8 (sz 10)) 
//     = ((cast bytes.[ sz 1 ] &. 3s) <<! 8l |. cast bytes.[ sz 0 ] &. 255s) == 1234s
//                          //    2                                     8
// let deserialize__10_int (bytes: t_Array u8 (sz 10)) = 
// let deserialize_10_int (bytes: t_Array u8 (sz 10))

let invert #t #a #b ($f: (x:t -> Lemma (a x == b x))) (x: t): Lemma (b x == a x)
    = f x

let r_to_l (lems:list term) : Tac unit =
    let first_or_trefl () : Tac unit =
        fold_left (fun k l () ->
                    (fun () -> apply_lemma_rw (`(invert (`#l))))
                    `or_else` k)
                  trefl lems () in
    pointwise first_or_trefl

let make_integers_generic () =
    pointwise (fun _ ->
       dump "X";
       match let?# t = expect_cur_formula_comp () in
             let?# n = expect_int_literal t in
             // let is_int = 
             //   try let x = tc (top_env ()) (`(3 + (`#t))) in
             //       print ("tc -> -> " ^ term_to_string x);
             //       true 
             //   with | _ -> false
             // in
             let ty = tc (cur_env ()) t in
             let ty = norm_term [iota; zeta; reify_; delta; primops; unmeta] ty in
             let ty = inspect_unascribe ty in
             let is_int = term_eq ty (`int) || term_eq ty (`nat) in
             fail ("unify=" ^ string_of_bool is_int);
             None
             // fail ("ty=" ^ term_to_string ty);
             // if unify ty `int
             // then 
             // unify
             // match?# expect_fvar ty with
             // | "Prims.int" -> None
             // | _ -> Some n
       with
        | Some n -> 
          let n = n + 1 in
          trefl ()
          // fail (string_of_int n)
        | _ -> trefl ()
    )


// let _ = FStar.Int16.__int_to_t
let _ = fun x -> assert (2s == x)
    by (
      norm [iota; primops]; make_integers_generic (); fail "x")

#push-options "--compat_pre_core 0"
let asdsd (bytes: t_Array u8 (sz 10))
    = let cast: u8 -> i16 = cast in
      assert (
             get_bit ((cast bytes.[ sz 3 ] &. 63s <: i16) <<! 4l |. cast bytes.[ sz 2 ] >>! 4l) (sz 3) == 0
      ) by (
        r_to_l rw_integers_list;
        fail "x";
        // l_to_r [`resugar_integer];
        // apply_lemma_rw (`rw_rhs_bit_or_no_mask);
        // compute ();
        // apply_lemma_rw (`rw_rhs_bit_or_no_mask);
        pointwise' (fun _ -> 
           // let _ = let?# t = expect_cur_formula_comp () in
           //         let?# (f, _) = expect_app_n t 3 in
           //         let?# () = expect_free_var f (`%get_bit) in
           //         apply_lemma_rw (`rw_rhs_bit_or_no_mask);
           //         invert ();
           //         Some (dump "heey")
           // in
           trefl ()
           // let _ = repeat clear_top in
           // dump "X";
           // (fun _ -> apply_lemma_rw (`rw_rhs_bit_or_no_mask)) `or_else` trefl;
           // let _ = repeat clear_top in
           // dump "Y"
        );
        fail "x"
      )

let fff bytes x: unit = 
    assert (
       get_bit (Seq.index (deserialize_10_int' bytes) 2) (sz 3) == 0
    ) by (
      compute'' ();
      // l_to_r [`rewrite_to_zero];
      // compute'' ();
      // apply_lemma_rw 
      // l_to_r [`rw_rhs_bit_or_no_mask];
      fail "DONE";
      focus (tadmit)
    );
    ()

