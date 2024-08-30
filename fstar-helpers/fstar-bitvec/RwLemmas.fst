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

open BitVecEq


let compute_one_round (): Tac _ =
   norm [ iota; zeta; reify_
          ; delta_namespace [
              "FStar"
            ; "BitVecEq"
            ; implode_qn (cur_module ())
            ; "MkSeq"
            ; `%Rust_primitives.Hax.array_of_list
          ]
        ; primops; unmeta];
   dump "X1";
   trace "compute_one_round: norm_pow2"        norm_pow2;
   dump "X2";
   trace "compute_one_round: norm_machine_int" norm_machine_int;
   dump "X3";
   trace "compute_one_round: norm_index"       Tactics.Seq.norm_index;
   dump "X4";
   ()


/// Proves a goal of the shape `forall (i:nat{i < N}). get_bit ... i == get_bit ... i` (`N` is expected to be a literal)
let prove_bit_vector_equality' (): Tac unit = 
  dump "A";
  norm [
    iota;
    primops;
    delta_only [`%bit_vec_of_int_t_array; `%FunctionalExtensionality.on];
    delta_namespace [
      implode_qn (cur_module ());
      "Libcrux_intrinsics.Avx2_extract";
      "BitVec.Intrinsics";
      "BitVecEq";
    ];
  ];
  dump "B";
  compute_one_round ();
  dump "C";
  prove_forall_nat_pointwise ( fun _ -> 
    Tactics.Seq.norm_index_minimal ();
    l_to_r [`bit_vec_to_int_t_lemma];
    print ("Ask SMT: " ^ term_to_string (cur_goal ()));
    focus smt_sync
  )
let prove_bit_vector_equality (): Tac unit = 
  set_rlimit 100;
  with_compat_pre_core 0 prove_bit_vector_equality'



let bit_vec_equal_elim (#n: nat) (#m:nat{n == m}) (bv1: bit_vec n) (bv2: bit_vec m) ()
  : Lemma (requires bit_vec_equal #n bv1 bv2)
          (ensures eq2 #(bit_vec n) bv1 (retype bv2))
  = bit_vec_equal_elim bv1 (retype bv2)

let prove_int_t_array_bitwise_eq
       #t1 #t2 #n1 #n2
       (arr1: t_Array (int_t t1) n1) (d1: num_bits t1)
       (arr2: t_Array (int_t t2) n2) (d2: num_bits t2 {v n1 * d1 == v n2 * d2})
       (#[(
           let _ = tc (cur_env ()) (cur_goal ()) in
           // Tactics.GetBit.prove_bit_vector_equality ()
           prove_bit_vector_equality ()
         )]proof: squash (forall (i: nat {i < v n1 * d1}). bit_vec_of_int_t_array arr1 d1 i == bit_vec_of_int_t_array arr2 d2 i))
       ()
     : Lemma (bit_vec_of_int_t_array arr1 d1 == bit_vec_of_int_t_array arr2 d2)
     = bit_vec_equal_intro_principle ();
       bit_vec_equal_elim (bit_vec_of_int_t_array arr1 d1) (bit_vec_of_int_t_array arr2 d2) ()

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
  
#push-options "--compat_pre_core 0"
#push-options "--z3rlimit 80"
let fff_ (bytes: t_Array u8 (sz 10)) x: unit = 
    let bv1 = bit_vec_of_int_t_array bytes 8 in
    let out = deserialize_10_int' bytes in
    let bv2 = bit_vec_of_int_t_array out 10 in
    assert (forall (i: nat { i < 80 }). bv1 i == bv2 i) by (
      Tactics.GetBit.prove_bit_vector_equality ()
    )
#pop-options

