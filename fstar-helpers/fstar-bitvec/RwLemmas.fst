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
#pop-options

let deserialize_10_int' (bytes: t_Array u8 (sz 10)): t_Array i16 (sz 8)
    = MkSeq.create8 (deserialize_10_int bytes)

let compute_one_round (): Tac _ =
   norm [ iota; zeta; reify_
        ; delta_namespace ["FStar"; "RwLemmas"; "MkSeq"]
        ; primops; unmeta];
   print "compute_one_round: light norm done";
   norm_pow2 ();
   print "compute_one_round: norm_pow2 done";
   Tactics.Seq.simplify_index_seq_of_list ();
   print "compute_one_round: simplify_index_seq_of_list done";
   norm_machine_int ();
   print "compute_one_round: norm_machine_int done";
   Tactics.Seq.norm_list_index ();
   print "compute_one_round: norm_list_index done"

let compute' (): Tac unit
    = 
      let rec fixpoint (): Tac _ =
          dump' "compute";
          let goal0 = cur_goal () in
          compute_one_round ();
          let goal1 = cur_goal () in
          if not (term_eq goal0 goal1) then fixpoint ()
      in 
      print "compute': start";
      fixpoint ();
      print "compute': done"

let opts = "--using_facts_from '-* +Rust_primitives.BitVectors
+Rust_primitives.Integers.get_bit_cast +Rust_primitives.Integers.get_bit_and +Rust_primitives.Integers.get_bit_or +Rust_primitives.Integers.get_bit_shl +Rust_primitives.Integers.get_bit_shr +Rust_primitives.Integers.get_bit_cast_extend' --fuel 0 --ifuel 0"

let _split_forall_nat
  (upper_bound: pos)
  ($p: (i:nat{i < upper_bound}) -> Type0)
  : Lemma (requires (if upper_bound = 0 then True
                     else p (upper_bound - 1) /\ (forall (i:nat{i < upper_bound - 1}). p i)))
          (ensures forall (i:nat{i < upper_bound}). p i)
  = ()

let rec prove_forall_pointwise (tactic: unit -> Tac unit): Tac unit
  = print ("prove_forall_pointwise: " ^ term_to_string (cur_goal ()));
    apply_lemma (`_split_forall_nat);
    trivial `or_else` (fun _ -> 
      if try norm [primops];
             split ();
             true
         with | e -> false
      then (
        tactic ();
        prove_forall_pointwise tactic
      )
    )

// #push-options "--using_facts_from '+ -FStar.Seq +Rust_primitives -Core -Lib +Rust_primitives.BitVectors +Rust_primitives.Integers.get_bit_cast +Rust_primitives.Integers +Lib.IntTypes +Rust_primitives.Integers.get_bit_or +Rust_primitives.Integers.get_bit_shl +Rust_primitives.Integers.get_bit_shr +Rust_primitives.Integers.get_bit_cast_extend +FStar'"
#restart-solver


let get_bit_or_zero_left #t (x y: int_t t) (i: nat)
  : Lemma (requires get_bit x i == 0)
          (ensures  get_bit (x |. y) i == get_bit y i)
          [SMTPat (get_bit (x |. y) i)]
  = get_bit_or x y i
let get_bit_or_zero_right #t (x y: int_t t) (i: nat)
  : Lemma (requires get_bit y i == 0)
          (ensures  get_bit (x |. y) i == get_bit x i)
          [SMTPat (get_bit (x |. y) i)]
  = get_bit_or x y i


#push-options "--compat_pre_core 0"
// #push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
#push-options "--z3rlimit 80"
let fff_ (bytes: t_Array u8 (sz 10)) x: unit = 
    let bv1 = bit_vec_of_int_t_array bytes 8 in
    let out = deserialize_10_int' bytes in
    let bv2 = bit_vec_of_int_t_array out 10 in
    // let lhs = ((cast (bytes.[ sz 1 ] <: u8) <: i16) &. 3s <: i16) <<! 8l <: i16 in
    // let rhs = (cast (bytes.[ sz 0 ] <: u8) <: i16) &. 255s <: i16 in
    // let goal = get_bit (bytes.[ sz 0 ] <: u8) 2 in
    // assert (
    //   get_bit ((((cast (bytes.[ sz 1 ] <: u8) <: i16) &. 3s <: i16) <<! 8l <: i16) |.
    //   ((cast (bytes.[ sz 0 ] <: u8) <: i16) &. 255s <: i16)) 2
    //   == get_bit (bytes.[ sz 0 ] <: u8) 2
    // )

    assert (forall (i: nat { i < 80 }). bv1 i == bv2 i) by (
      // set_options opts;
      norm [
        iota; primops; 
        delta_only [`%bit_vec_of_int_t_array; `%FunctionalExtensionality.on; `%deserialize_10_int'; `%deserialize_10_int];
      ];
      compute_one_round ();
      prove_forall_pointwise (fun _ -> 
        Tactics.Seq.norm_list_index ();
        dump' "Send to SMT";
        set_rlimit 80;
        let _ = repeat clear_top in
        focus smt_sync;
        dump' "solved!";
        ()
      )
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

