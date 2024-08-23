module Hello

open Core
open FStar.Mul
open FStar.Tactics.V2

// module _ = BitVecEq
// module _ = Rust_primitives.BitVectors

// // val ( >>! ) #t #t': int_t -> int

// #push-options "--admit_smt_queries true"
// val serialize_10_int (v: t_Slice i16)
//     : Prims.Pure (u8 & u8 & u8 & u8 & u8)
//       (requires (Core.Slice.impl__len #i16 v <: usize) =. sz 4)
//       (ensures fun _ -> True)
// let serialize_10_int (v: t_Slice i16) =
//   let r0:u8 = cast ((v.[ sz 0 ] <: i16) &. 255s <: i16) <: u8 in
//   let r1:u8 =
//     ((cast ((v.[ sz 1 ] <: i16) &. 63s <: i16) <: u8) <<! 2l <: u8) |.
//     (cast (((v.[ sz 0 ] <: i16) >>! 8l <: i16) &. 3s <: i16) <: u8)
//   in
//   let r2:u8 =
//     ((cast ((v.[ sz 2 ] <: i16) &. 15s <: i16) <: u8) <<! 4l <: u8) |.
//     (cast (((v.[ sz 1 ] <: i16) >>! 6l <: i16) &. 15s <: i16) <: u8)
//   in
//   let r3:u8 =
//     ((cast ((v.[ sz 3 ] <: i16) &. 3s <: i16) <: u8) <<! 6l <: u8) |.
//     (cast (((v.[ sz 2 ] <: i16) >>! 4l <: i16) &. 63s <: i16) <: u8)
//   in
//   let r4:u8 = cast (((v.[ sz 3 ] <: i16) >>! 2l <: i16) &. 255s <: i16) <: u8 in
//   //let _:Prims.unit = BitVecEq.bit_vec_equal_intro_principle () in
//   r0, r1, r2, r3, r4 <: (u8 & u8 & u8 & u8 & u8)
// #pop-options

// let wrapped (v: t_Array i16 (sz 4)): t_Array u8 (sz 5) =
//   MkSeq.create5 (serialize_10_int v)

// let norm_seq #t (l: list t) i
//     : Lemma (Seq.Base.index (Seq.Base.seq_of_list l) i == FStar.List.Tot.index l i) 
//     = ()

// let split_forall_nat
//   (#upper_bound: pos)
//   (p: (i:nat{i <= upper_bound}) -> Type0)
//   : Lemma (requires (if upper_bound = 0 then True else (forall (i:nat{i <= upper_bound - 1}). p i))
//                    /\ p upper_bound
//           )
//           (ensures forall (i:nat{i <= upper_bound}). p i)
//   = ()

// let rw_simplify_v_mk_int t (x: int {Rust_primitives.Integers.range x t})
//   : Lemma (v (mk_int #t x) == x)
//   = ()

  
// let rw_simplify_v_mk_intu8 
//   (x: int {Rust_primitives.Integers.range x u8_inttype})
//   (t: _ {t == u8_inttype})
//   : Lemma (UInt8.v (mk_int #t x) == x)
//   = assert (UInt8.v (mk_int #t x) == v (mk_int #u8_inttype x))


// let conv_mk_int_u8 x: Lemma (mk_int #u8_inttype x == UInt8.uint_to_t x) = admit ()
// let rw_v_uint_to_t_u8 x: Lemma (UInt8.v (UInt8.uint_to_t x) == x) = ()
// let rw_v_uint_to_t_u8' x: Lemma (UInt8.uint_to_t (UInt8.v x) == x) = ()
// let rw_v_u8 x: Lemma (v #u8_inttype x == UInt8.v x) = ()

// let conv_mk_int_i16 x: Lemma (mk_int #i16_inttype x == Int16.int_to_t x) = admit ()
// let rw_v_uint_to_t_i16 x: Lemma (Int16.v (Int16.int_to_t x) == x) = ()
// let rw_v_uint_to_t_i16' x: Lemma (Int16.int_to_t (Int16.v x) == x) = ()
// let rw_v_i16 x: Lemma (v #i16_inttype x == Int16.v x) = ()

// let conv_mk_int_i32 x: Lemma (mk_int #i32_inttype x == Int32.int_to_t x) = admit ()
// let rw_v_uint_to_t_i32 x: Lemma (Int32.v (Int32.int_to_t x) == x) = ()
// let rw_v_uint_to_t_i32' x: Lemma (Int32.int_to_t (Int32.v x) == x) = ()
// let rw_v_i32 x: Lemma (v #i32_inttype x == Int32.v x) = ()

// let usize_v_mk_int x: Lemma (v #usize_inttype (mk_int #usize_inttype x) == x) = ()

// let rw_ints = [
//   `conv_mk_int_u8;
//   `rw_v_uint_to_t_u8;
//   `rw_v_uint_to_t_u8';
//   `rw_v_u8;
//   `conv_mk_int_i16;
//   `rw_v_uint_to_t_i16;
//   `rw_v_uint_to_t_i16';
//   `rw_v_i16;
//   `conv_mk_int_i32;
//   `rw_v_uint_to_t_i32;
//   `rw_v_uint_to_t_i32';
//   `rw_v_i32;
//   `usize_v_mk_int;
// ]

// let rw_v_mk_int t x: Lemma (v (mk_int #t x) == x) = ()

// // let lemma_gt_0 x: Lemma (
// //      (Int16.v (logand #Lib.IntTypes.S16 x 255s) @%. Lib.IntTypes.U8 >= 0)
// //   == (Int16.v x >= 0)
// //   ) = ()

// let rw = [
//     `norm_seq
//   ; `rw_simplify_v_mk_int
//   ; `conv_mk_int_u8;  `rw_v_uint_to_t_u8;  `rw_v_uint_to_t_u8'
//   ; `conv_mk_int_i16; `rw_v_uint_to_t_i16; `rw_v_uint_to_t_i16'
//   ; `rw_v_mk_int
//   // ; `lemma_gt_0
// ]

// #push-options "--z3rlimit 60"
// let rw_bit_or (b1 b2: bit) result:
//   Lemma 
//     (requires (
//         (b1 = 0 ==> b2 = 0 ==> result = 0)
//       /\ (b1 = 0 ==> b2 = 1 ==> result = 1)
//       /\ (b1 = 1 ==> b2 = 0 ==> result = 1)
//       /\ (b1 = 1 ==> b2 = 1 ==> result = 0)
//     ))
//     (ensures (bit_or b1 b2 == result))
//     = ()

// type nn = {
//   x_bits: nat;
//   y_bits: int;
//   x_shift: nat;
// }

// #push-options "--z3rlimit 260"
// let numbers
//   t (u: inttype {bits t > bits u})
//   (d1: num_bits t) (d2: num_bits u)
//   (arr2_term_idx: nat) =
//   // let t (arr2_term_idx: nat {arr2_term_idx > 0 /\ arr2_term_idx < 4}) =
//   let first_bit = arr2_term_idx * d2 in
//   let arr1_idx = first_bit / d1 in
//   let x_shift = first_bit % d1 in
//   // How many bits are left from `x` in the result?
//   let x_bits: nat = d1 - x_shift in
//   // How many bits are left from `y` in the result?
//   let y_bits: int = d2 - x_bits in
//   // let x_mask = pow2 x_bits - 1 in
//   // let y_mask = pow2 y_bits - 1 in
//   {x_bits;    y_bits;       x_shift;  }
// #pop-options

// let config = numbers i16_inttype u8_inttype 10 8 2

// #push-options "--z3rlimit 260"
// // #push-options "--z3rlimit 260 --admit_smt_queries true"
// let compute_term
//   t (u: inttype {bits t > bits u})
//   (d1: num_bits t) (d2: num_bits u)
//   (n1: nat) (n2: nat {n2 * d2 == n1 * d1})
//   (arr1: Seq.seq (int_t t) {Seq.length arr1 == n1})
//   (arr2: Seq.seq (int_t u) {Seq.length arr2 == n2})
//   (arr2_term_idx: nat {arr2_term_idx < n2}): int_t u =
//   // let t (arr2_term_idx: nat {arr2_term_idx > 0 /\ arr2_term_idx < 4}) =
//   let first_bit = arr2_term_idx * d2 in
//   let arr1_idx = first_bit / d1 in
//   let x = Seq.index arr1 arr1_idx in
//   let x_shift = first_bit % d1 in
//   // How many bits are left from `x` in the result?
//   let x_bits = d1 - x_shift in
//   // How many bits are left from `y` in the result?
//   let y_bits = d2 - x_bits in
//   Math.Lemmas.pow2_le_compat (bits t - (if unsigned t then 0 else 1)) x_bits;
//   let x_mask = pow2 x_bits - 1 in
//   let x': int_t u = cast ((x >>! mk_int #i32_inttype x_shift) &. mk_int #t x_mask) in
//   if arr1_idx + 1 < n1 && y_bits > 0
//   then (
//     Math.Lemmas.pow2_le_compat (bits u - (if unsigned u then 0 else 1)) y_bits;
//     let y_mask = pow2 y_bits - 1 in
//     let y = Seq.index arr1 (arr1_idx + 1) in
//     let y': int_t u = cast (y &. mk_int #t y_mask) in
//     let y_shift = x_bits in
//     let y': int_t u = y' <<! mk_int #i32_inttype y_shift in
//     y' |. x'
//   ) else x'
// #pop-options

// #push-options "--z3rlimit 60 --admit_smt_queries true"
// let lemma_compute_term 
//   t (u: inttype {bits t > bits u})
//   (d1: num_bits t) (d2: num_bits u)
//   (n1: nat) (n2: nat {n2 * d2 == n1 * d1})
//   (arr1: Seq.seq (int_t t) {Seq.length arr1 == n1})
//   (arr2: Seq.seq (int_t u) {Seq.length arr2 == n2})
//   (arr2_term_idx: nat {arr2_term_idx < n2})
//   (i: nat { i < d2 })
//   : Lemma (
//      let first_bit = arr2_term_idx * d2 in
//      let x_bits = d1 - first_bit % d1 in
//      let arr1_idx = first_bit / d1 in
//      get_bit (compute_term t u d1 d2 n1 n2 arr1 arr2 arr2_term_idx) (sz i)
//   == ( if i < x_bits
//                                       // ICI C'EST PAS OKAY
//        then get_bit (Seq.index arr1 arr1_idx      ) (sz i)
//        else get_bit (Seq.index arr1 (arr1_idx + 1)) (sz (i - x_bits))
//      )
//      // let j = i - 
//      // bv1 i == get_bit (compute_term t u d1 d2 n1 n2 arr1 arr2 arr2_term_idx) j
//   ) = admit ()
// #pop-options  

// let norm_pow2 (): Tac unit =
//   pointwise (fun () -> 
//     begin match FStar.Tactics.V2.Logic.cur_formula () with
//     | Comp _eq lhs _rhs ->         
//         let (head, args) = collect_app lhs in
//         ( match (inspect head, args) with
//         | (Tv_FVar fv, [_]) -> 
//           if implode_qn (inspect_fv fv) = `%pow2
//           then norm [iota; zeta_full; reify_; delta; primops; unmeta]
//           else ()
//         | _ -> ())
//     | _ -> ()
//     end;
//     trefl ())

// let unfold_index (#a: Type) (l: list a) (i:nat{i < List.Tot.length l})
//   : Lemma (  FStar.List.Tot.index #a l i 
//           == (let hd::tl = l in
//               if i = 0 then hd else List.Tot.index tl (i - 1)))
//   = ()

// exception StopNormIndex

// let norm_index (): Tac unit =
//   let _ = repeat (fun _ ->
//     lset "found" false;
//     pointwise (fun _ ->
//       (fun () -> 
//         apply_lemma_rw (`unfold_index);
//         lset "found" true
//       ) `or_else` trefl);
//     if lget "found" then () else raise StopNormIndex) in ()

// // #push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
// // let xx (x0 x1: i16) = 
// //   get_bit_pow2_minus_one_i16 63 (sz 3);
// //   assert (get_bit (mk_int #i16_inttype 63) (sz 3) == 1)
  
// //   // get_bit_pow2_minus_one_i16 63 (sz 3);
// //   assert (
// //      get_bit x1 (mk_int #usize_inttype 3)
// //   == 
// //      // get_bit ((cast (x1 &. mk_int #i16_inttype 63) <: u8) <<! mk_int #i16_inttype 2)
// //      //         (mk_int 5)
// //      // get_bit (cast (x1 &. mk_int #i16_inttype 63) <: u8)
// //      get_bit (x1 &. mk_int #i16_inttype 63)
// //              (mk_int 3)
// //      // bit_or 
// //      //  (get_bit ((cast (x1 &. mk_int #i16_inttype 63) <: u8) <<! mk_int #i16_inttype 2) (mk_int 5))
// //      //  (get_bit (cast (x0 >>! mk_int #i16_inttype 8 &. mk_int #i16_inttype 3) <: u8) (mk_int 5))
// //   )

// // let shift_right_simplify_0 t (x: int_t t): Lemma (shift_right x 0l == x)
// //   = ()

// #push-options "--compat_pre_core 0"
// #push-options "--z3rlimit 60"
// let lemma (arr1: t_Array i16 (sz 4)) = 
//     let arr2 = wrapped arr1 in
//     let d1 = 10 in
//     let d2 = 8 in
//     let bv1 = bit_vec_of_int_t_array arr1 d1 in
//     let bv2 = bit_vec_of_int_t_array arr2 d2 in
//     let mk = compute_term
//                i16_inttype u8_inttype 
//                10 8
//                4  5
//                arr1 arr2
//     in
//     let mk_lemma = lemma_compute_term
//                i16_inttype u8_inttype 
//                10 8
//                4  5
//                arr1 arr2
//     in
//     let i = 13 in
//     assert (forall (i: nat {i <= 19}). bv1 i == bv2 i) by (
//       let rec round (i: nat): Tac _ = 
//         apply_lemma (`split_forall_nat);
//         norm [iota; reify_; primops; unmeta; delta_only [`%op_Subtraction]];
//         let deep_norm () = 
//           norm [iota; zeta; reify_; delta; primops; unmeta];
//           norm_index ();
//           l_to_r (rw_ints `List.Tot.append` [`norm_index; `norm_seq])
//         in
//         split ();
//         flip ();
//         focus (fun () ->
//           dump "x";
//           let t = quote (get_bit (mk (i / d2)) (sz (i % d2))) in
//           // let bv2_eq_t = tcut (`((`@bv2) (`@i) == (`#t))) in
//           grewrite (quote (bv2 i)) t;
//           dump "after grewrite 1";
//           flip ();
//           focus (fun _ -> 
//             let _ = repeatn 3 deep_norm in
//             trefl `or_else` (fun () -> 
//               dump "Not refl after norm, SMT?";
//               smt_sync ();
//               dump "SMT ok"
//             )
//           );
//           // let bv1_eq_t = tcut (`((`@bv1) (`@i) == (`#t))) in
//           grewrite (quote (bv1 i)) t;
//           dump "after grewrite 2";
//           flip ();
//           focus (fun () ->
//             dump "dunm";
//             l_to_r [quote mk_lemma];
//             compute ();
//             trefl `or_else` (fun () -> 
//               dump "Not refl, SMT?";
//               smt_sync ();
//               dump "SMT ok"
//             )
//           );
//           dump "Just before the end of the round";
//           deep_norm ();
//           dump "Just before the end of the round (+norm)";
//           trefl ()
//         );
//         dump ("finished round" ^ string_of_int i);
//         if i = 0
//         then ()
//         else round (i - 1)
//       in 
//       let _ = round 19 in
//       ()
//     );
//     // assert (bv2 i == get_bit (mk (i / d2)) (sz (i % d2))) by (
//     // );
//     // assert (
//     //   bv2 8 == get_bit t (sz 0)
//     // ) by (
//     //   compute ();
//     //   l_to_r [`norm_seq];
//     // );
//     admit();
//     ()

// let _ =
//     assume (Int16.v (Seq.Base.index arr1 (i / d1)) >= 0);
//     assume (Int16.v (Seq.Base.index arr1 (i / d2)) >= 0);
//     // assert (bv2 13 == );
//     assert (
//            bv2 13
//         == bv1 13
//         // == get_bit (Seq.index bv1 0) (sz 0)
//         // == get_bit (Seq.index arr2 0) (sz 0)
//         //get_bit (Seq.index arr2 0) (sz 0)
//     ) by (
    
//         compute ();
//         l_to_r rw;
//         compute ();
//         l_to_r rw;
//         norm [iota; simplify; zeta_full; reify_; delta; primops; unmeta];
//         l_to_r rw;
//         l_to_r [`Math.Lemmas.modulo_distributivity];
//         l_to_r [`get_bit_or; `get_bit_and];
//         // l_to_r [`rw_bit_or];
//         apply_lemma (`rw_bit_or);
//         l_to_r rw;
//         fail "x";
//         let _ = repeat split in
//         iterAll (fun _ -> 
//           l_to_r rw;
//           norm [iota; simplify; zeta_full; reify_; delta; primops; simplify; unmeta];
//           ()
//         );
//         fail "x";
//         iterAll (
//           fun _ -> 
//             dump "SMT for:";
//             smt_sync ()
//         )
//         // let _ = iterAll (fun _ -> let _ = l_intros () in ()) in
//         // fail "x"
//         // tadmit ()
//     )



