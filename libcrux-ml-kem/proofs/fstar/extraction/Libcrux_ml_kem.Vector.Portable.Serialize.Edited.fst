module Libcrux_ml_kem.Vector.Portable.Serialize.Edited
// #set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
// open Core
// open FStar.Mul

// #push-options "--admit_smt_queries true"

// let deserialize_10_int (bytes: t_Slice u8) =
//   let r0:i16 =
//     (((cast (bytes.[ sz 1 ] <: u8) <: i16) &. 3s <: i16) <<! 8l <: i16) |.
//     ((cast (bytes.[ sz 0 ] <: u8) <: i16) &. 255s <: i16)
//   in
//   let r1:i16 =
//     (((cast (bytes.[ sz 2 ] <: u8) <: i16) &. 15s <: i16) <<! 6l <: i16) |.
//     ((cast (bytes.[ sz 1 ] <: u8) <: i16) >>! 2l <: i16)
//   in
//   let r2:i16 =
//     (((cast (bytes.[ sz 3 ] <: u8) <: i16) &. 63s <: i16) <<! 4l <: i16) |.
//     ((cast (bytes.[ sz 2 ] <: u8) <: i16) >>! 4l <: i16)
//   in
//   let r3:i16 =
//     ((cast (bytes.[ sz 4 ] <: u8) <: i16) <<! 2l <: i16) |.
//     ((cast (bytes.[ sz 3 ] <: u8) <: i16) >>! 6l <: i16)
//   in
//   let r4:i16 =
//     (((cast (bytes.[ sz 6 ] <: u8) <: i16) &. 3s <: i16) <<! 8l <: i16) |.
//     ((cast (bytes.[ sz 5 ] <: u8) <: i16) &. 255s <: i16)
//   in
//   let r5:i16 =
//     (((cast (bytes.[ sz 7 ] <: u8) <: i16) &. 15s <: i16) <<! 6l <: i16) |.
//     ((cast (bytes.[ sz 6 ] <: u8) <: i16) >>! 2l <: i16)
//   in
//   let r6:i16 =
//     (((cast (bytes.[ sz 8 ] <: u8) <: i16) &. 63s <: i16) <<! 4l <: i16) |.
//     ((cast (bytes.[ sz 7 ] <: u8) <: i16) >>! 4l <: i16)
//   in
//   let r7:i16 =
//     ((cast (bytes.[ sz 9 ] <: u8) <: i16) <<! 2l <: i16) |.
//     ((cast (bytes.[ sz 8 ] <: u8) <: i16) >>! 6l <: i16)
//   in
//   r0, r1, r2, r3, r4, r5, r6, r7 <: (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)

// #pop-options

// #push-options "--admit_smt_queries true"

// let deserialize_11_int (bytes: t_Slice u8) =
//   let r0:i16 =
//     (((cast (bytes.[ sz 1 ] <: u8) <: i16) &. 7s <: i16) <<! 8l <: i16) |.
//     (cast (bytes.[ sz 0 ] <: u8) <: i16)
//   in
//   let r1:i16 =
//     (((cast (bytes.[ sz 2 ] <: u8) <: i16) &. 63s <: i16) <<! 5l <: i16) |.
//     ((cast (bytes.[ sz 1 ] <: u8) <: i16) >>! 3l <: i16)
//   in
//   let r2:i16 =
//     ((((cast (bytes.[ sz 4 ] <: u8) <: i16) &. 1s <: i16) <<! 10l <: i16) |.
//       ((cast (bytes.[ sz 3 ] <: u8) <: i16) <<! 2l <: i16)
//       <:
//       i16) |.
//     ((cast (bytes.[ sz 2 ] <: u8) <: i16) >>! 6l <: i16)
//   in
//   let r3:i16 =
//     (((cast (bytes.[ sz 5 ] <: u8) <: i16) &. 15s <: i16) <<! 7l <: i16) |.
//     ((cast (bytes.[ sz 4 ] <: u8) <: i16) >>! 1l <: i16)
//   in
//   let r4:i16 =
//     (((cast (bytes.[ sz 6 ] <: u8) <: i16) &. 127s <: i16) <<! 4l <: i16) |.
//     ((cast (bytes.[ sz 5 ] <: u8) <: i16) >>! 4l <: i16)
//   in
//   let r5:i16 =
//     ((((cast (bytes.[ sz 8 ] <: u8) <: i16) &. 3s <: i16) <<! 9l <: i16) |.
//       ((cast (bytes.[ sz 7 ] <: u8) <: i16) <<! 1l <: i16)
//       <:
//       i16) |.
//     ((cast (bytes.[ sz 6 ] <: u8) <: i16) >>! 7l <: i16)
//   in
//   let r6:i16 =
//     (((cast (bytes.[ sz 9 ] <: u8) <: i16) &. 31s <: i16) <<! 6l <: i16) |.
//     ((cast (bytes.[ sz 8 ] <: u8) <: i16) >>! 2l <: i16)
//   in
//   let r7:i16 =
//     ((cast (bytes.[ sz 10 ] <: u8) <: i16) <<! 3l <: i16) |.
//     ((cast (bytes.[ sz 9 ] <: u8) <: i16) >>! 5l <: i16)
//   in
//   r0, r1, r2, r3, r4, r5, r6, r7 <: (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)

// #pop-options

// #push-options "--admit_smt_queries true"

// let deserialize_12_int (bytes: t_Slice u8) =
//   let byte0:i16 = cast (bytes.[ sz 0 ] <: u8) <: i16 in
//   let byte1:i16 = cast (bytes.[ sz 1 ] <: u8) <: i16 in
//   let byte2:i16 = cast (bytes.[ sz 2 ] <: u8) <: i16 in
//   let r0:i16 = ((byte1 &. 15s <: i16) <<! 8l <: i16) |. (byte0 &. 255s <: i16) in
//   let r1:i16 = (byte2 <<! 4l <: i16) |. ((byte1 >>! 4l <: i16) &. 15s <: i16) in
//   r0, r1 <: (i16 & i16)

// #pop-options

// #push-options "--admit_smt_queries true"

// let deserialize_4_int (bytes: t_Slice u8) =
//   let v0:i16 = cast ((bytes.[ sz 0 ] <: u8) &. 15uy <: u8) <: i16 in
//   let v1:i16 = cast (((bytes.[ sz 0 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16 in
//   let v2:i16 = cast ((bytes.[ sz 1 ] <: u8) &. 15uy <: u8) <: i16 in
//   let v3:i16 = cast (((bytes.[ sz 1 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16 in
//   let v4:i16 = cast ((bytes.[ sz 2 ] <: u8) &. 15uy <: u8) <: i16 in
//   let v5:i16 = cast (((bytes.[ sz 2 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16 in
//   let v6:i16 = cast ((bytes.[ sz 3 ] <: u8) &. 15uy <: u8) <: i16 in
//   let v7:i16 = cast (((bytes.[ sz 3 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16 in
//   v0, v1, v2, v3, v4, v5, v6, v7 <: (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)

// #pop-options

// #push-options "--admit_smt_queries true"

// let deserialize_5_int (bytes: t_Slice u8) =
//   let v0:i16 = cast ((bytes.[ sz 0 ] <: u8) &. 31uy <: u8) <: i16 in
//   let v1:i16 =
//     cast ((((bytes.[ sz 1 ] <: u8) &. 3uy <: u8) <<! 3l <: u8) |.
//         ((bytes.[ sz 0 ] <: u8) >>! 5l <: u8)
//         <:
//         u8)
//     <:
//     i16
//   in
//   let v2:i16 = cast (((bytes.[ sz 1 ] <: u8) >>! 2l <: u8) &. 31uy <: u8) <: i16 in
//   let v3:i16 =
//     cast ((((bytes.[ sz 2 ] <: u8) &. 15uy <: u8) <<! 1l <: u8) |.
//         ((bytes.[ sz 1 ] <: u8) >>! 7l <: u8)
//         <:
//         u8)
//     <:
//     i16
//   in
//   let v4:i16 =
//     cast ((((bytes.[ sz 3 ] <: u8) &. 1uy <: u8) <<! 4l <: u8) |.
//         ((bytes.[ sz 2 ] <: u8) >>! 4l <: u8)
//         <:
//         u8)
//     <:
//     i16
//   in
//   let v5:i16 = cast (((bytes.[ sz 3 ] <: u8) >>! 1l <: u8) &. 31uy <: u8) <: i16 in
//   let v6:i16 =
//     cast ((((bytes.[ sz 4 ] <: u8) &. 7uy <: u8) <<! 2l <: u8) |.
//         ((bytes.[ sz 3 ] <: u8) >>! 6l <: u8)
//         <:
//         u8)
//     <:
//     i16
//   in
//   let v7:i16 = cast ((bytes.[ sz 4 ] <: u8) >>! 3l <: u8) <: i16 in
//   v0, v1, v2, v3, v4, v5, v6, v7 <: (i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16)

// #pop-options

// #push-options "--z3rlimit 480 --split_queries always"

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
//   let _:Prims.unit = BitVecEq.bit_vec_equal_intro_principle () in
//   r0, r1, r2, r3, r4 <: (u8 & u8 & u8 & u8 & u8)

// #pop-options

// // #push-options "--ifuel 1 --z3rlimit 1600 "

// unfold let (.[]) (x: t_Slice i16) (i: usize {v i < Seq.length x}): i16 = Seq.index x (v i)

// // val serialize_11_int' (v: t_Slice i16)
// //     : Prims.Pure (u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8)
// //       (requires Seq.length v == 8 
// //               /\ Rust_primitives.bounded (v.[sz 0] <: i16) 11
// //               /\ Rust_primitives.bounded (v.[sz 1] <: i16) 11
// //               /\ Rust_primitives.bounded (v.[sz 2] <: i16) 11
// //               /\ Rust_primitives.bounded (v.[sz 3] <: i16) 11
// //               /\ Rust_primitives.bounded (v.[sz 4] <: i16) 11
// //               /\ Rust_primitives.bounded (v.[sz 5] <: i16) 11
// //               /\ Rust_primitives.bounded (v.[sz 6] <: i16) 11
// //               /\ Rust_primitives.bounded (v.[sz 7] <: i16) 11
// //               )
// //       (ensures
// //         fun tuple ->
// //           let tuple:(u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8) = tuple in
// //           BitVecEq.int_t_array_bitwise_eq' (v <: t_Array i16 (sz 8)) 11 (MkSeq.create11 tuple) 8)

// #push-options "--ifuel 1 --z3rlimit 600 --split_queries always"

// val compress_coefficients_11_
//       (coefficient1 coefficient2 coefficient3 coefficient4 coefficient5 coefficient6 coefficient7 coefficient8:
//           int_t_d i16_inttype 11)
//     : Prims.Pure (u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8)
//       (requires True)
//       (ensures fun tuple ->
//         True
//          // BitVecEq.int_t_array_bitwise_eq'
//          //        (MkSeq.create8 (coefficient1, coefficient2, coefficient3, coefficient4, coefficient5, coefficient6, coefficient7, coefficient8)) 11
//          //        (MkSeq.create11 tuple) 8
//       )

// #pop-options

// // #push-options "--z3rlimit 90"
// // let rightmost_bits #t u 
// //   (coef: int_t t) (n_bits: nat {n_bits <= bits t - (if unsigned t then 0 else 1)})
// //   (shift: nat {shift > 0 /\ shift < bits u})
// //   : result: int_t u {forall i. get_bit result i == }
// //   = Math.Lemmas.pow2_le_compat (bits t - (if unsigned t then 0 else 1)) n_bits;
// //         (cast (coef &. mk_int (pow2 n_bits - 1)) <: int_t u) 
// //     <<! (mk_int shift <: int_t u)
// open FStar.Tactics.V2
// // let rightmost_bits #t (u: _ {bits t >= bits u})
// //   (coef: int_t t)
// //   (n_bits: nat {n_bits <= bits t - (if unsigned t then 0 else 1)})
// //   (shift: nat {shift > 0 /\ shift < (bits u - n_bits)})
// //   // : result: int_t u 
// //   //   {forall (i: nat). i < n_bits  ==> get_bit result (sz i) == get_bit coef (sz (i - shift)) }
// //   // : result: int_t u {forall i. (i >= shift /\ i < shift + n_bits)
// //   //                      ==> get_bit result (sz i) == get_bit coef (sz (i - shift))
// //   //                   }
// //   = Math.Lemmas.pow2_le_compat (bits t - (if unsigned t then 0 else 1)) n_bits;
// //     let x = (cast (coef &. mk_int (pow2 n_bits - 1)) <: int_t u) in
// //     let y: int_t u = mk_int shift  in
// //     let result = x <<! y in
// //     // // let i = sz 0 in
// //     // // get_bit_shl x y i;
// //     // admitP (forall i.
// //     //   (ensures get_bit (x <<! y) i
// //     //             == (if v i < v y then 0 else get_bit x (mk_int (v i - v y))))
// //     // );
// //     // // assert (
// //     // //   n_bits > 0
// //     // // ==>
// //     // //   (get_bit result (sz 0) == get_bit x (sz shift))
// //     // // );
// //     // // admit ();
// //     result

// // let leftmost_bits #t u (coef: int_t t) (shift: nat {shift > 0 /\ shift < bits t})
// //   = (cast (coef >>! (mk_int shift <: int_t t)) <: int_t u)

// let is_num_bits t (d:nat) = d > 0 /\ d <= bits t /\ (signed t ==> d < bits t)

// #push-options "--fuel 0 --ifuel 0 --z3rlimit 900"
// [@@"opaque_to_smt"]
// let mix_two_ints t (u:inttype {bits t > bits u})
//   (d1: num_bits t) (d2: num_bits u)
//   (x1: int_t t) (x2: int_t t)
//   (offset1: pos { offset1 < d1 /\ offset1 > d1 - d2})
//   : r: int_t u { 
//     forall i. i < d2
//       ==> get_bit r (sz i)
//        = ( if i >= d1 - offset1 (* offset2 *)
//            then
//              // get_bit r (sz i)
//              get_bit x2 (sz (i - (d1 - offset1)))
//            else
//              // get_bit r (sz i)
//              get_bit x1 (sz (offset1 + i))
//          )
//   }
//   = 
//     let offset2 = d1 - offset1 in
//     Math.Lemmas.pow2_le_compat (bits t - (if unsigned t then 0 else 1)) (d2 - offset2);
//     let power = d2 - offset2 in
//     FStar.Classical.forall_intro (get_bit_pow2_minus_one #t power);
//     let mask: int_t t = mk_int (pow2 power - 1) in
//     admit ();
//     ((cast (x2 &. mask <: int_t t) <: int_t u) <<! mk_int #t offset2 <: int_t u) |.
//        (cast (x1 >>! mk_int #t offset1 <: int_t t) <: int_t u)
//     // let a = cast (x1 >>! mk_int #t offset1 <: int_t t) <: int_t u in
//     // let b' = cast (x2 &. mask <: int_t t) <: int_t u in
//     // let b = b' <<! mk_int #t offset2 <: int_t u in
//     // introduce forall (i: nat {i >= offset2 /\ i < d2}). get_bit b (sz i) == get_bit x2 (sz (i - offset2))
//     // with (
//     //   get_bit_pow2_minus_one #t power (sz (i - offset2));
//     //   get_bit_and x2 mask (sz i)
//     // );
//     // let proof (i: nat {i >= offset2 /\ i < d2}) = 
//     //   // assert (get_bit b (sz i)  == get_bit b' (sz (i - offset2)));
//     //   get_bit_pow2_minus_one #t power (sz (i - offset2));
//     //   // assert (get_bit mask (sz (i - offset2)) == 1);
//     //   get_bit_and x2 mask (sz i);
//     //   // assert (get_bit b' (sz (i - offset2)) == get_bit x2 (sz (i - offset2)));
//     //   assert (get_bit b (sz i) == get_bit x2 (sz (i - offset2)));
//     //   ()
//     // in
//     // // assert (forall (i: nat {i < offset2}). get_bit b (sz i) == 0);
//     // // let proof (i: nat {i < offset2}) = 
     
//     // //   calc (==) {
//     // //        get_bit r (sz i);
//     // //     == {
//     // //       assert (get_bit b (sz i) == 0);
//     // //       get_bit_or a b (sz i)
//     // //     } get_bit a (sz i);
//     // //     // == {
//     // //     //   get_bit_shr x1 (mk_int #t offset1) (sz i)
//     // //     // } get_bit x1 (sz (offset1 + i));
//     // //   };
//     // //   // assert (get_bit b (sz i) == 0);
//     // //   // assert (get_bit (b |. a) (sz i) == get_bit a (sz i));
//     // //   // assert (get_bit a (sz i) == get_bit x1 (sz (offset1 + i)));
//     // //   // assert (get_bit (b |. a) (sz i) == get_bit x1 (sz (offset1 + i)));
//     // //   ()
//     // //   // assert (get_bit r (a |. b) == get_bit a (sz i));
//     // // in
//     // r
// #pop-options

// let mask_inv_opt_in_range #t (mask: int_t t {Some? (mask_inv_opt (v mask))})
//   : Lemma (Rust_primitives.Integers.range (Some?.v (mask_inv_opt (v mask))) t)
//           [SMTPat (Rust_primitives.Integers.range (Some?.v (mask_inv_opt (v mask))) t)]
//   = let n = (Some?.v (mask_inv_opt (v mask))) in
//     assert (pow2 n - 1 == v mask)

// #push-options "--z3rlimit 90 --split_queries always"
// let rw_mix_two_ints
//   t u 
//   (x1: int_t t) (x2: int_t t)
//   (mask: int_t t {Some? (mask_inv_opt (v mask))})
//   (shl: int_t t {v shl > 0 /\ v shl < bits u})
//   (shr: int_t t {v shr > 0 /\ v shr < bits t})
//     : Lemma 
//     (requires (
//       let d1 = v shl + v shr in
//       let d2 = Some?.v (mask_inv_opt (v mask)) + v shl in
//       let offset1 = v shr in
//         bits t > bits u
//       /\ is_num_bits t d1
//       /\ is_num_bits u d2
//       /\ offset1 < d1
//       /\ offset1 > d1 - d2
//     ))
//     (ensures
//          ( ((cast (x2 &. mask <: int_t t) <: int_t u) <<! shl <: int_t u) 
//          |. (cast (x1 >>! shr <: int_t t) <: int_t u)
//          )
//          == (
//            let d1 = v shl + v shr in
//            let d2 = Some?.v (mask_inv_opt (v mask)) + v shl in
//            let offset1 = v shr in
//            mix_two_ints t u d1 d2 x1 x2 offset1
//          )
//     )
//     = let d1 = v shl + v shr in
//       let d2 = Some?.v (mask_inv_opt (v mask)) + v shl in
//       let offset1 = v shr in
//       reveal_opaque (`%mix_two_ints) (mix_two_ints t u d1 d2 x1 x2 offset1);
//       admit ()
// #pop-options

// open FStar.Tactics.V2

// let tau ()
//   = let first_or_trefl () : Tac unit =
//       if try apply_lemma_rw (`rw_mix_two_ints); true
//          with | _ -> false
//       then begin
//         FStar.Tactics.V1.dump "Before norm";
//         norm [iota; zeta_full; reify_; delta; primops; simplify; unmeta];
//         FStar.Tactics.V1.dump "After norm";
//         trivial ()
//       end else trefl () 
//     in
//     pointwise first_or_trefl;
//     FStar.Tactics.V1.dump "xx";
//     trefl ()

// #push-options "--compat_pre_core 2"

// #push-options "--z3rlimit 90"
// // [@@"opaque_to_smt"]
// [@@postprocess_with tau]
// let compress_coefficients_11_
//       coefficient1 coefficient2 coefficient3 coefficient4 coefficient5 coefficient6 coefficient7 coefficient8 =
//   let coef1:u8 = cast (coefficient1 <: i16) <: u8 in
//   // assert (get_bit )
//   // coefficient1
//   let coef2:u8 =
//     ((cast (coefficient2 &. 31s <: i16) <: u8) <<! 3s <: u8) |.
//     (cast (coefficient1 >>! 8s <: i16) <: u8)
//   in
//   let coef3:u8 =
//     ((cast (coefficient3 &. 3s <: i16) <: u8) <<! 6s <: u8) |.
//     (cast (coefficient2 >>! 5s <: i16) <: u8)
//   in
//   let coef4:u8 = cast ((coefficient3 >>! 2s <: i16) &. 255s <: i16) <: u8 in
//   let coef5:u8 =
//     ((cast (coefficient4 &. 127s <: i16) <: u8) <<! 1s <: u8) |.
//     (cast (coefficient3 >>! 10s <: i16) <: u8)
//   in
//   let coef6:u8 =
//     ((cast (coefficient5 &. 15s <: i16) <: u8) <<! 4s <: u8) |.
//     (cast (coefficient4 >>! 7s <: i16) <: u8)
//   in
//   let coef7:u8 =
//     ((cast (coefficient6 &. 1s <: i16) <: u8) <<! 7s <: u8) |.
//     (cast (coefficient5 >>! 4s <: i16) <: u8)
//   in
//   let coef8:u8 = cast ((coefficient6 >>! 1s <: i16) &. 255s <: i16) <: u8 in
//   let coef9:u8 =
//     ((cast (coefficient7 &. 63s <: i16) <: u8) <<! 2s <: u8) |.
//     (cast (coefficient6 >>! 9s <: i16) <: u8)
//   in
//   let coef10:u8 =
//     ((cast (coefficient8 &. 7s <: i16) <: u8) <<! 5s <: u8) |.
//     (cast (coefficient7 >>! 6s <: i16) <: u8)
//   in
//   let coef11:u8 = cast (coefficient8 >>! 3s <: i16) <: u8 in
//   // admit ();
//   // BitVecEq.bit_vec_equal_intro_principle ();
//   coef1, coef2, coef3, coef4, coef5, coef6, coef7, coef8, coef9, coef10, coef11
//   <:
//   (u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8)
// #pop-options

// #push-options "--fuel 5 --ifuel 0 --z3rlimit 800 --split_queries always"
// let compress_coefficients_11_lemma
//       (coefficient1 coefficient2 coefficient3 coefficient4 coefficient5 coefficient6 coefficient7 coefficient8:
//           int_t_d i16_inttype 11)
//     = BitVecEq.bit_vec_equal_intro_principle ();
//       // let arr1 = MkSeq.create8 (coefficient1, coefficient2, coefficient3, coefficient4, coefficient5, coefficient6, coefficient7, coefficient8) in
//       // let arr2 = (MkSeq.create11 (compress_coefficients_11_ coefficient1 coefficient2 coefficient3 coefficient4 coefficient5 coefficient6 coefficient7 coefficient8)) in
//       // let bv1 = bit_vec_of_int_t_array arr1 11 in
//       // let bv2 = bit_vec_of_int_t_array arr2 8 in
//       // let d1 = 11 in
//       // let d2 = 8 in
//       // let i = 27 in
//       // let coef_number_input = i / d1 in
//       // let mixed = mix_two_ints i16_inttype u8_inttype
//       //       11 8
//       //       (Seq.index arr1 coef_number_input      )
//       //       (Seq.index arr1 (coef_number_input + 1))
//       //       (i % d2) in
//       assert (
//         // bv1 i == get_bit (Seq.index arr1 (coef_number_input)) (sz (i % d1))
//         // bv2 i == get_bit mixed (sz (i % d2))
//             // get_bit (Seq.index arr1 (coef_number_input)) (sz (i % d1))
//         // bv1 27 == bv2 27
//          BitVecEq.int_t_array_bitwise_eq'
//                 (MkSeq.create8 (coefficient1, coefficient2, coefficient3, coefficient4, coefficient5, coefficient6, coefficient7, coefficient8)) 11
//                 (MkSeq.create11 (compress_coefficients_11_ coefficient1 coefficient2 coefficient3 coefficient4 coefficient5 coefficient6 coefficient7 coefficient8)) 8
//       )
// #pop-options

// // bv2 i == bit_vec (Seq.index arr1 ()) 

// let eee
//       (coefficient1 coefficient2 coefficient3 coefficient4 coefficient5 coefficient6 coefficient7 coefficient8:
//           int_t_d i32_inttype 11)
//     = let arr1 = MkSeq.create8 (coefficient1, coefficient2, coefficient3, coefficient4, coefficient5, coefficient6, coefficient7, coefficient8) in
//       let tuple = compress_coefficients_11_
//       coefficient1 coefficient2 coefficient3 coefficient4 coefficient5 coefficient6 coefficient7 coefficient8 in
//       let arr2 = MkSeq.create11 tuple in
//       let bv1 = bit_vec_of_int_t_array arr1 11 in
//       let bv2 = bit_vec_of_int_t_array (MkSeq.create11 tuple) 8 in
//       let i = 0 in
//       let d = 11 in
//       assert (
//         // bv2 i == get_bit (Seq.index arr2 (i / 11)) (sz (i % 11))
//         bv2 i == (cast (coefficient1 <: i32) <: u8)
//       ) by (FStar.Tactics.compute (); FStar.Tactics.trefl (); FStar.Tactics.fail "x");
//       // assert (
//       //   bv1 i == get_bit (Seq.index arr1 (i / 11)) (sz (i % 11))
//       // ) by (FStar.Tactics.compute (); FStar.Tactics.fail "x");
//       admit ()
//     // : Prims.Pure (u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8)
//     //   (requires True)
//     //   (ensures fun tuple ->
//     //      BitVecEq.int_t_array_bitwise_eq'
//     //             (MkSeq.create8 (coefficient1, coefficient2, coefficient3, coefficient4, coefficient5, coefficient6, coefficient7, coefficient8)) 11
//     //             (MkSeq.create11 tuple) 8
//     //   )

// #push-options "--ifuel 1 --z3rlimit 200"

// #push-options "--z3rlimit 1600 --split_queries always"

// let serialize_11_int' (v: t_Slice i16) =
//   let r0:u8 = cast (v.[ sz 0 ] <: i16) <: u8 in
//   let r1:u8 =
//     ((cast ((v.[ sz 1 ] <: i16) &. 31s <: i16) <: u8) <<! 3l <: u8) |.
//     (cast ((v.[ sz 0 ] <: i16) >>! 8l <: i16) <: u8)
//   in
//   let r2:u8 =
//     ((cast ((v.[ sz 2 ] <: i16) &. 3s <: i16) <: u8) <<! 6l <: u8) |.
//     (cast ((v.[ sz 1 ] <: i16) >>! 5l <: i16) <: u8)
//   in
//   let r3:u8 = cast (((v.[ sz 2 ] <: i16) >>! 2l <: i16) &. 255s <: i16) <: u8 in
//   let r4:u8 =
//     ((cast ((v.[ sz 3 ] <: i16) &. 127s <: i16) <: u8) <<! 1l <: u8) |.
//     (cast ((v.[ sz 2 ] <: i16) >>! 10l <: i16) <: u8)
//   in
//   let r5:u8 =
//     ((cast ((v.[ sz 4 ] <: i16) &. 15s <: i16) <: u8) <<! 4l <: u8) |.
//     (cast ((v.[ sz 3 ] <: i16) >>! 7l <: i16) <: u8)
//   in
//   let r6:u8 =
//     ((cast ((v.[ sz 5 ] <: i16) &. 1s <: i16) <: u8) <<! 7l <: u8) |.
//     (cast ((v.[ sz 4 ] <: i16) >>! 4l <: i16) <: u8)
//   in
//   let r7:u8 = cast (((v.[ sz 5 ] <: i16) >>! 1l <: i16) &. 255s <: i16) <: u8 in
//   let r8:u8 =
//     ((cast ((v.[ sz 6 ] <: i16) &. 63s <: i16) <: u8) <<! 2l <: u8) |.
//     (cast ((v.[ sz 5 ] <: i16) >>! 9l <: i16) <: u8)
//   in
//   let r9:u8 =
//     ((cast ((v.[ sz 7 ] <: i16) &. 7s <: i16) <: u8) <<! 5l <: u8) |.
//     (cast ((v.[ sz 6 ] <: i16) >>! 6l <: i16) <: u8)
//   in
//   let r10: u8 = (cast ((v.[ sz 7 ] <: i16) >>! 3l <: i16) <: u8) in
//   let _:Prims.unit = BitVecEq.bit_vec_equal_intro_principle () in
//   r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10
//   <:
//   (u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8)

// #pop-options

// #push-options "--admit_smt_queries true"

// let serialize_12_int (v: t_Slice i16) =
//   let r0:u8 = cast ((v.[ sz 0 ] <: i16) &. 255s <: i16) <: u8 in
//   let r1:u8 =
//     cast (((v.[ sz 0 ] <: i16) >>! 8l <: i16) |. (((v.[ sz 1 ] <: i16) &. 15s <: i16) <<! 4l <: i16)
//         <:
//         i16)
//     <:
//     u8
//   in
//   let r2:u8 = cast (((v.[ sz 1 ] <: i16) >>! 4l <: i16) &. 255s <: i16) <: u8 in
//   r0, r1, r2 <: (u8 & u8 & u8)

// #pop-options

// #push-options "--admit_smt_queries true"

// let serialize_4_int (v: t_Slice i16) =
//   let result0:u8 =
//     ((cast (v.[ sz 1 ] <: i16) <: u8) <<! 4l <: u8) |. (cast (v.[ sz 0 ] <: i16) <: u8)
//   in
//   let result1:u8 =
//     ((cast (v.[ sz 3 ] <: i16) <: u8) <<! 4l <: u8) |. (cast (v.[ sz 2 ] <: i16) <: u8)
//   in
//   let result2:u8 =
//     ((cast (v.[ sz 5 ] <: i16) <: u8) <<! 4l <: u8) |. (cast (v.[ sz 4 ] <: i16) <: u8)
//   in
//   let result3:u8 =
//     ((cast (v.[ sz 7 ] <: i16) <: u8) <<! 4l <: u8) |. (cast (v.[ sz 6 ] <: i16) <: u8)
//   in
//   result0, result1, result2, result3 <: (u8 & u8 & u8 & u8)

// #pop-options

// #push-options "--admit_smt_queries true"

// let serialize_5_int (v: t_Slice i16) =
//   let r0:u8 = cast ((v.[ sz 0 ] <: i16) |. ((v.[ sz 1 ] <: i16) <<! 5l <: i16) <: i16) <: u8 in
//   let r1:u8 =
//     cast ((((v.[ sz 1 ] <: i16) >>! 3l <: i16) |. ((v.[ sz 2 ] <: i16) <<! 2l <: i16) <: i16) |.
//         ((v.[ sz 3 ] <: i16) <<! 7l <: i16)
//         <:
//         i16)
//     <:
//     u8
//   in
//   let r2:u8 =
//     cast (((v.[ sz 3 ] <: i16) >>! 1l <: i16) |. ((v.[ sz 4 ] <: i16) <<! 4l <: i16) <: i16) <: u8
//   in
//   let r3:u8 =
//     cast ((((v.[ sz 4 ] <: i16) >>! 4l <: i16) |. ((v.[ sz 5 ] <: i16) <<! 1l <: i16) <: i16) |.
//         ((v.[ sz 6 ] <: i16) <<! 6l <: i16)
//         <:
//         i16)
//     <:
//     u8
//   in
//   let r4:u8 =
//     cast (((v.[ sz 6 ] <: i16) >>! 2l <: i16) |. ((v.[ sz 7 ] <: i16) <<! 3l <: i16) <: i16) <: u8
//   in
//   r0, r1, r2, r3, r4 <: (u8 & u8 & u8 & u8 & u8)

// #pop-options

// #push-options "--admit_smt_queries true"

// let serialize_1_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
//   let result:t_Array u8 (sz 2) = Rust_primitives.Hax.repeat 0uy (sz 2) in
//   let result:t_Array u8 (sz 2) =
//     Rust_primitives.Hax.Folds.fold_range (sz 0)
//       (sz 8)
//       (fun result temp_1_ ->
//           let result:t_Array u8 (sz 2) = result in
//           let _:usize = temp_1_ in
//           true)
//       result
//       (fun result i ->
//           let result:t_Array u8 (sz 2) = result in
//           let i:usize = i in
//           Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
//             (sz 0)
//             ((result.[ sz 0 ] <: u8) |.
//               ((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) <: u8) <<!
//                 i
//                 <:
//                 u8)
//               <:
//               u8)
//           <:
//           t_Array u8 (sz 2))
//   in
//   let result:t_Array u8 (sz 2) =
//     Rust_primitives.Hax.Folds.fold_range (sz 8)
//       (sz 16)
//       (fun result temp_1_ ->
//           let result:t_Array u8 (sz 2) = result in
//           let _:usize = temp_1_ in
//           true)
//       result
//       (fun result i ->
//           let result:t_Array u8 (sz 2) = result in
//           let i:usize = i in
//           Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
//             (sz 1)
//             ((result.[ sz 1 ] <: u8) |.
//               ((cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) <: u8) <<!
//                 (i -! sz 8 <: usize)
//                 <:
//                 u8)
//               <:
//               u8)
//           <:
//           t_Array u8 (sz 2))
//   in
//   result

// #pop-options

// #push-options "--admit_smt_queries true"

// let serialize_10_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
//   let r0_4_:(u8 & u8 & u8 & u8 & u8) =
//     serialize_10_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
//             Core.Ops.Range.f_start = sz 0;
//             Core.Ops.Range.f_end = sz 4
//           }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice i16)
//   in
//   let r5_9_:(u8 & u8 & u8 & u8 & u8) =
//     serialize_10_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
//             Core.Ops.Range.f_start = sz 4;
//             Core.Ops.Range.f_end = sz 8
//           }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice i16)
//   in
//   let r10_14_:(u8 & u8 & u8 & u8 & u8) =
//     serialize_10_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
//             Core.Ops.Range.f_start = sz 8;
//             Core.Ops.Range.f_end = sz 12
//           }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice i16)
//   in
//   let r15_19_:(u8 & u8 & u8 & u8 & u8) =
//     serialize_10_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
//             Core.Ops.Range.f_start = sz 12;
//             Core.Ops.Range.f_end = sz 16
//           }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice i16)
//   in
//   let list =
//     [
//       r0_4_._1; r0_4_._2; r0_4_._3; r0_4_._4; r0_4_._5; r5_9_._1; r5_9_._2; r5_9_._3; r5_9_._4;
//       r5_9_._5; r10_14_._1; r10_14_._2; r10_14_._3; r10_14_._4; r10_14_._5; r15_19_._1; r15_19_._2;
//       r15_19_._3; r15_19_._4; r15_19_._5
//     ]
//   in
//   FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 20);
//   Rust_primitives.Hax.array_of_list 20 list

// #pop-options

// #push-options "--admit_smt_queries true"

// let serialize_11_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
//   let r0_10_:(u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8) =
//     serialize_11_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
//             Core.Ops.Range.f_start = sz 0;
//             Core.Ops.Range.f_end = sz 8
//           }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice i16)
//   in
//   let r11_21_:(u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8) =
//     serialize_11_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
//             Core.Ops.Range.f_start = sz 8;
//             Core.Ops.Range.f_end = sz 16
//           }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice i16)
//   in
//   let result:t_Array u8 (sz 22) = Rust_primitives.Hax.repeat 0uy (sz 22) in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 0) r0_10_._1
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 1) r0_10_._2
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 2) r0_10_._3
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 3) r0_10_._4
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 4) r0_10_._5
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 5) r0_10_._6
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 6) r0_10_._7
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 7) r0_10_._8
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 8) r0_10_._9
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 9) r0_10_._10
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 10) r0_10_._11
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 11) r11_21_._1
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 12) r11_21_._2
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 13) r11_21_._3
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 14) r11_21_._4
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 15) r11_21_._5
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 16) r11_21_._6
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 17) r11_21_._7
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 18) r11_21_._8
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 19) r11_21_._9
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 20) r11_21_._10
//   in
//   let result:t_Array u8 (sz 22) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 21) r11_21_._11
//   in
//   result

// #pop-options

// #push-options "--admit_smt_queries true"

// let serialize_12_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
//   let r0_2_:(u8 & u8 & u8) =
//     serialize_12_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
//             Core.Ops.Range.f_start = sz 0;
//             Core.Ops.Range.f_end = sz 2
//           }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice i16)
//   in
//   let r3_5_:(u8 & u8 & u8) =
//     serialize_12_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
//             Core.Ops.Range.f_start = sz 2;
//             Core.Ops.Range.f_end = sz 4
//           }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice i16)
//   in
//   let r6_8_:(u8 & u8 & u8) =
//     serialize_12_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
//             Core.Ops.Range.f_start = sz 4;
//             Core.Ops.Range.f_end = sz 6
//           }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice i16)
//   in
//   let r9_11_:(u8 & u8 & u8) =
//     serialize_12_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
//             Core.Ops.Range.f_start = sz 6;
//             Core.Ops.Range.f_end = sz 8
//           }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice i16)
//   in
//   let r12_14_:(u8 & u8 & u8) =
//     serialize_12_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
//             Core.Ops.Range.f_start = sz 8;
//             Core.Ops.Range.f_end = sz 10
//           }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice i16)
//   in
//   let r15_17_:(u8 & u8 & u8) =
//     serialize_12_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
//             Core.Ops.Range.f_start = sz 10;
//             Core.Ops.Range.f_end = sz 12
//           }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice i16)
//   in
//   let r18_20_:(u8 & u8 & u8) =
//     serialize_12_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
//             Core.Ops.Range.f_start = sz 12;
//             Core.Ops.Range.f_end = sz 14
//           }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice i16)
//   in
//   let r21_23_:(u8 & u8 & u8) =
//     serialize_12_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
//             Core.Ops.Range.f_start = sz 14;
//             Core.Ops.Range.f_end = sz 16
//           }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice i16)
//   in
//   let result:t_Array u8 (sz 24) = Rust_primitives.Hax.repeat 0uy (sz 24) in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 0) r0_2_._1
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 1) r0_2_._2
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 2) r0_2_._3
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 3) r3_5_._1
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 4) r3_5_._2
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 5) r3_5_._3
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 6) r6_8_._1
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 7) r6_8_._2
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 8) r6_8_._3
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 9) r9_11_._1
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 10) r9_11_._2
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 11) r9_11_._3
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 12) r12_14_._1
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 13) r12_14_._2
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 14) r12_14_._3
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 15) r15_17_._1
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 16) r15_17_._2
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 17) r15_17_._3
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 18) r18_20_._1
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 19) r18_20_._2
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 20) r18_20_._3
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 21) r21_23_._1
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 22) r21_23_._2
//   in
//   let result:t_Array u8 (sz 24) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 23) r21_23_._3
//   in
//   result

// #pop-options

// #push-options "--admit_smt_queries true"

// let serialize_4_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
//   let result0_3_:(u8 & u8 & u8 & u8) =
//     serialize_4_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
//             Core.Ops.Range.f_start = sz 0;
//             Core.Ops.Range.f_end = sz 8
//           }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice i16)
//   in
//   let result4_7_:(u8 & u8 & u8 & u8) =
//     serialize_4_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
//             Core.Ops.Range.f_start = sz 8;
//             Core.Ops.Range.f_end = sz 16
//           }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice i16)
//   in
//   let result:t_Array u8 (sz 8) = Rust_primitives.Hax.repeat 0uy (sz 8) in
//   let result:t_Array u8 (sz 8) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 0) result0_3_._1
//   in
//   let result:t_Array u8 (sz 8) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 1) result0_3_._2
//   in
//   let result:t_Array u8 (sz 8) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 2) result0_3_._3
//   in
//   let result:t_Array u8 (sz 8) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 3) result0_3_._4
//   in
//   let result:t_Array u8 (sz 8) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 4) result4_7_._1
//   in
//   let result:t_Array u8 (sz 8) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 5) result4_7_._2
//   in
//   let result:t_Array u8 (sz 8) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 6) result4_7_._3
//   in
//   let result:t_Array u8 (sz 8) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 7) result4_7_._4
//   in
//   result

// #pop-options

// #push-options "--admit_smt_queries true"

// let serialize_5_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
//   let r0_4_:(u8 & u8 & u8 & u8 & u8) =
//     serialize_5_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
//             Core.Ops.Range.f_start = sz 0;
//             Core.Ops.Range.f_end = sz 8
//           }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice i16)
//   in
//   let r5_9_:(u8 & u8 & u8 & u8 & u8) =
//     serialize_5_int (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ {
//             Core.Ops.Range.f_start = sz 8;
//             Core.Ops.Range.f_end = sz 16
//           }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice i16)
//   in
//   let result:t_Array u8 (sz 10) = Rust_primitives.Hax.repeat 0uy (sz 10) in
//   let result:t_Array u8 (sz 10) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 0) r0_4_._1
//   in
//   let result:t_Array u8 (sz 10) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 1) r0_4_._2
//   in
//   let result:t_Array u8 (sz 10) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 2) r0_4_._3
//   in
//   let result:t_Array u8 (sz 10) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 3) r0_4_._4
//   in
//   let result:t_Array u8 (sz 10) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 4) r0_4_._5
//   in
//   let result:t_Array u8 (sz 10) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 5) r5_9_._1
//   in
//   let result:t_Array u8 (sz 10) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 6) r5_9_._2
//   in
//   let result:t_Array u8 (sz 10) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 7) r5_9_._3
//   in
//   let result:t_Array u8 (sz 10) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 8) r5_9_._4
//   in
//   let result:t_Array u8 (sz 10) =
//     Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (sz 9) r5_9_._5
//   in
//   result

// #pop-options

// #push-options "--admit_smt_queries true"

// let deserialize_1_ (v: t_Slice u8) =
//   let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     Libcrux_ml_kem.Vector.Portable.Vector_type.zero ()
//   in
//   let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     Rust_primitives.Hax.Folds.fold_range (sz 0)
//       (sz 8)
//       (fun result temp_1_ ->
//           let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
//           let _:usize = temp_1_ in
//           true)
//       result
//       (fun result i ->
//           let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
//           let i:usize = i in
//           {
//             result with
//             Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//             =
//             Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
//                 .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//               i
//               (cast (((v.[ sz 0 ] <: u8) >>! i <: u8) &. 1uy <: u8) <: i16)
//             <:
//             t_Array i16 (sz 16)
//           }
//           <:
//           Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
//   in
//   let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     Rust_primitives.Hax.Folds.fold_range (sz 8)
//       Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
//       (fun result temp_1_ ->
//           let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
//           let _:usize = temp_1_ in
//           true)
//       result
//       (fun result i ->
//           let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
//           let i:usize = i in
//           {
//             result with
//             Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//             =
//             Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
//                 .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//               i
//               (cast (((v.[ sz 1 ] <: u8) >>! (i -! sz 8 <: usize) <: u8) &. 1uy <: u8) <: i16)
//             <:
//             t_Array i16 (sz 16)
//           }
//           <:
//           Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
//   in
//   result

// #pop-options

// #push-options "--admit_smt_queries true"

// let deserialize_10_ (bytes: t_Slice u8) =
//   let v0_7_:(i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16) =
//     deserialize_10_int (bytes.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 10 }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice u8)
//   in
//   let v8_15_:(i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16) =
//     deserialize_10_int (bytes.[ { Core.Ops.Range.f_start = sz 10; Core.Ops.Range.f_end = sz 20 }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice u8)
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     Libcrux_ml_kem.Vector.Portable.Vector_type.zero ()
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 0)
//         v0_7_._1
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 1)
//         v0_7_._2
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 2)
//         v0_7_._3
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 3)
//         v0_7_._4
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 4)
//         v0_7_._5
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 5)
//         v0_7_._6
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 6)
//         v0_7_._7
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 7)
//         v0_7_._8
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 8)
//         v8_15_._1
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 9)
//         v8_15_._2
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 10)
//         v8_15_._3
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 11)
//         v8_15_._4
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 12)
//         v8_15_._5
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 13)
//         v8_15_._6
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 14)
//         v8_15_._7
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 15)
//         v8_15_._8
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   v

// #pop-options

// #push-options "--admit_smt_queries true"

// let deserialize_11_ (bytes: t_Slice u8) =
//   let v0_7_:(i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16) =
//     deserialize_11_int (bytes.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 11 }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice u8)
//   in
//   let v8_15_:(i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16) =
//     deserialize_11_int (bytes.[ { Core.Ops.Range.f_start = sz 11; Core.Ops.Range.f_end = sz 22 }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice u8)
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     Libcrux_ml_kem.Vector.Portable.Vector_type.zero ()
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 0)
//         v0_7_._1
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 1)
//         v0_7_._2
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 2)
//         v0_7_._3
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 3)
//         v0_7_._4
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 4)
//         v0_7_._5
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 5)
//         v0_7_._6
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 6)
//         v0_7_._7
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 7)
//         v0_7_._8
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 8)
//         v8_15_._1
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 9)
//         v8_15_._2
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 10)
//         v8_15_._3
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 11)
//         v8_15_._4
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 12)
//         v8_15_._5
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 13)
//         v8_15_._6
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 14)
//         v8_15_._7
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 15)
//         v8_15_._8
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   v

// #pop-options

// #push-options "--admit_smt_queries true"

// let deserialize_12_ (bytes: t_Slice u8) =
//   let v0_1_:(i16 & i16) =
//     deserialize_12_int (bytes.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 3 }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice u8)
//   in
//   let v2_3_:(i16 & i16) =
//     deserialize_12_int (bytes.[ { Core.Ops.Range.f_start = sz 3; Core.Ops.Range.f_end = sz 6 }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice u8)
//   in
//   let v4_5_:(i16 & i16) =
//     deserialize_12_int (bytes.[ { Core.Ops.Range.f_start = sz 6; Core.Ops.Range.f_end = sz 9 }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice u8)
//   in
//   let v6_7_:(i16 & i16) =
//     deserialize_12_int (bytes.[ { Core.Ops.Range.f_start = sz 9; Core.Ops.Range.f_end = sz 12 }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice u8)
//   in
//   let v8_9_:(i16 & i16) =
//     deserialize_12_int (bytes.[ { Core.Ops.Range.f_start = sz 12; Core.Ops.Range.f_end = sz 15 }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice u8)
//   in
//   let v10_11_:(i16 & i16) =
//     deserialize_12_int (bytes.[ { Core.Ops.Range.f_start = sz 15; Core.Ops.Range.f_end = sz 18 }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice u8)
//   in
//   let v12_13_:(i16 & i16) =
//     deserialize_12_int (bytes.[ { Core.Ops.Range.f_start = sz 18; Core.Ops.Range.f_end = sz 21 }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice u8)
//   in
//   let v14_15_:(i16 & i16) =
//     deserialize_12_int (bytes.[ { Core.Ops.Range.f_start = sz 21; Core.Ops.Range.f_end = sz 24 }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice u8)
//   in
//   let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     Libcrux_ml_kem.Vector.Portable.Vector_type.zero ()
//   in
//   let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       re with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 0)
//         v0_1_._1
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       re with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 1)
//         v0_1_._2
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       re with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 2)
//         v2_3_._1
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       re with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 3)
//         v2_3_._2
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       re with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 4)
//         v4_5_._1
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       re with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 5)
//         v4_5_._2
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       re with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 6)
//         v6_7_._1
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       re with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 7)
//         v6_7_._2
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       re with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 8)
//         v8_9_._1
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       re with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 9)
//         v8_9_._2
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       re with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 10)
//         v10_11_._1
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       re with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 11)
//         v10_11_._2
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       re with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 12)
//         v12_13_._1
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       re with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 13)
//         v12_13_._2
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       re with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 14)
//         v14_15_._1
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let re:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       re with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 15)
//         v14_15_._2
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   re

// #pop-options

// #push-options "--admit_smt_queries true"

// let deserialize_4_ (bytes: t_Slice u8) =
//   let v0_7_:(i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16) =
//     deserialize_4_int (bytes.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 4 }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice u8)
//   in
//   let v8_15_:(i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16) =
//     deserialize_4_int (bytes.[ { Core.Ops.Range.f_start = sz 4; Core.Ops.Range.f_end = sz 8 }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice u8)
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     Libcrux_ml_kem.Vector.Portable.Vector_type.zero ()
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 0)
//         v0_7_._1
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 1)
//         v0_7_._2
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 2)
//         v0_7_._3
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 3)
//         v0_7_._4
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 4)
//         v0_7_._5
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 5)
//         v0_7_._6
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 6)
//         v0_7_._7
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 7)
//         v0_7_._8
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 8)
//         v8_15_._1
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 9)
//         v8_15_._2
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 10)
//         v8_15_._3
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 11)
//         v8_15_._4
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 12)
//         v8_15_._5
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 13)
//         v8_15_._6
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 14)
//         v8_15_._7
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 15)
//         v8_15_._8
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   v

// #pop-options

// #push-options "--admit_smt_queries true"

// let deserialize_5_ (bytes: t_Slice u8) =
//   let v0_7_:(i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16) =
//     deserialize_5_int (bytes.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 5 }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice u8)
//   in
//   let v8_15_:(i16 & i16 & i16 & i16 & i16 & i16 & i16 & i16) =
//     deserialize_5_int (bytes.[ { Core.Ops.Range.f_start = sz 5; Core.Ops.Range.f_end = sz 10 }
//           <:
//           Core.Ops.Range.t_Range usize ]
//         <:
//         t_Slice u8)
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     Libcrux_ml_kem.Vector.Portable.Vector_type.zero ()
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 0)
//         v0_7_._1
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 1)
//         v0_7_._2
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 2)
//         v0_7_._3
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 3)
//         v0_7_._4
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 4)
//         v0_7_._5
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 5)
//         v0_7_._6
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 6)
//         v0_7_._7
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 7)
//         v0_7_._8
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 8)
//         v8_15_._1
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 9)
//         v8_15_._2
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 10)
//         v8_15_._3
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 11)
//         v8_15_._4
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 12)
//         v8_15_._5
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 13)
//         v8_15_._6
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 14)
//         v8_15_._7
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
//     {
//       v with
//       Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//       =
//       Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
//           .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
//         (sz 15)
//         v8_15_._8
//     }
//     <:
//     Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
//   in
//   v

// #pop-options
