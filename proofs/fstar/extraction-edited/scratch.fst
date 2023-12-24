// let get_bit_nat (#n: inttype) (x: int_t n) (nth: nat {nth < 32}): bit
//   = v x / pow2 nth % 2

// let get_bit_list
//   (#n: inttype) (len: nat)
//   (l: list (int_t n))
//   (d: d_param_nat)
//   (nth: nat {nth < len * d})
//   : Pure bit (requires normalize (List.Tot.length l == len)) (ensures fun _ -> True)
//   = assert_norm (List.Tot.length l == len);
//     get_bit_nat (List.Tot.index l (nth / d)) (nth % d)

// val compress_coefficients_10_ (coefficient1 coefficient2 coefficient3 coefficient4: i32)
//     : Pure (u8 & u8 & u8 & u8 & u8) 
//       (requires True)
//       (requires fun (v1, v2, v3, v4, v5) -> (
//         let inputs:  t_Array i32 (sz 4) = createL [coefficient1; coefficient2; coefficient3; coefficient4] in
//         let outputs: t_Array u8 (sz 5) = createL [v1; v2; v3; v4; v5] in
//         let inputs_arr  = bit_vector_slice_arr inputs  (sz 10) in
//         let outputs_arr = bit_vector_slice_arr outputs (sz 8) in
//         // inputs `Seq.equal` outputs
//         let coef1:u8 = cast (coefficient1 &. 255l <: i32) <: u8 in
//         assert (outputs_arr.[sz 0] == get_bit_arr outputs (sz 8) (sz 0));
//         assert (get_bit_arr outputs (sz 8) (sz 0) == get_bit (outputs.[sz 0]) (sz 0));
//         let coef2:u8 =
//           ((cast (coefficient2 &. 63l <: i32) <: u8) <<! 2l <: u8) |.
//           (cast ((coefficient1 >>! 8l <: i32) &. 3l <: i32) <: u8)
//         in
//         // assert (get_bit coef1 (sz 0) == );
//         // outputs.[sz 0] == v1 /\
//         // outputs.[sz 1] == v2 /\
//         // get_bit coef1 (sz 0) == outputs_arr.[sz 0] /\
//         // get_bit coef2 (sz 0) == outputs_arr.[sz 8] /\        // get_bit coef2 (sz 1) == outputs_arr.[sz 1] /\
//         True
//         // inputs.[sz 0] == outputs.[sz 0]
//       ))
let get_byte_lemma
  #n
  (x:    int_t n)
  (mask: maskT n)
  (shift: int_t n {v shift >= 0 /\ v shift < bits n})
  (nth: usize {v nth < bits n})
  : Lemma (
         get_bit ((x &. mask) <<! shift) nth
      == ( if v nth >= v shift && v nth <= v shift + mask_inv mask 
           then get_bit x (nth -! sz (v shift))
           else 0
         )
    )
    [SMTPat (get_bit ((x &. mask) <<! shift) nth)]
  = admit ()

let term
  (#n: _ {LI.maxint n >= 255})
  (x y:    int_t n)
  (shift: int_t n {v shift > 0 /\ v shift < 8})
  (d: d_param n {v shift < v d})
  =  (cast (y &. mk_mask (8 - v shift)) <<! shift)
  |. (cast ((x >>! (Rust_primitives.Integers.cast d -! shift)) &. mk_mask (v shift)) <: u8)

// #push-options "--z3rlimit 50"
let get_byte_lemma'
  (#n: _ {LI.maxint n >= 255})
  (x xs xm y ym ys: int_t n)
  (nth: usize {v nth < bits LI.U8})
  : Lemma 
    (requires (
      v ys > 0 /\ v ys < bits LI.U8 /\
      v xs >= 0 /\ v xs < bits n     /\
      ym == mk_mask (8 - v ys) /\
      xm == mk_mask (v ys) /\
      (let shift = v ys in 
       let d = v xs + v ys in 
       shift < d /\ d > 0 /\ d < bits n)
    ))
    (ensures (
      let z: u8 = (cast (y &. ym) <<! ys)
               |. cast ((x >>! xs) &. xm)
      in
      let shift = ys in
      let d = v xs + v ys in
      assert (z == term x y shift (sz d));
      get_bit z nth
      == (if v nth < v shift
          then 
            ( assume (v nth < v xs);
              get_bit x (mk_int (v nth + v shift))
            )
          else 0)
    ))
    // [SMTPat [(( |. ) ((cast (x &. x_mask) <: u8) <<! x_shift <: u8)); y; nth]]
  = admit ()


// open FStar.Tactics
// let gen_get_bit_pow2_minus_one (signed: bool) (bits: nat) (x_log: nat): Tac sigelt
//   = let x = pow2 x_log - 1 in
//     let t_binder = fresh_binder_named "t" (`inttype) in
//     let nth_binder = fresh_binder_named "nth" (`usize) in
//     let nth = binder_to_term nth_binder in
//     let int_name = (if signed then "i" else "u") ^ string_of_int bits in
//     let inttype = pack (Tv_FVar (pack_fv [ "Rust_primitives"; "Integers"; int_name ^ "_inttype"])) in
//     let pre = `(v (`#nth) < `@bits /\ (`#t_binder) == (`#inttype)) in
//     let to_t = pack_fv [ "FStar"
//                        ; (if signed then "Int" else "UInt") ^ string_of_int bits
//                        ; if signed then "int_to_t" else "uint_to_t"] in
//     let to_t = pack (Tv_FVar to_t) in
//     let post = `(fun () -> get_bit #(`#inttype) ((`#to_t) (`@x)) (`#nth) == (if v (`#nth) < `@x_log then 1 else 0)) in
//     let bds = [t_binder; nth_binder] in
//     let sv = Sg_Let false [pack_lb {
//         lb_fv = pack_fv (cur_module () @ ["get_bit_pow2_minus_one_" ^ int_name ^ "_" ^ string_of_int x]);
//         lb_us = [];
//         lb_typ = mk_arr bds (pack_comp (C_Lemma pre post (`[SMTPat (get_bit #(`#t_binder) ((`#to_t) (`@x)) (`#nth))])));
//         lb_def = mk_abs bds (`( 
//           assert_norm (pow2 (`@x_log) - 1 == (`@x));
//           mk_int_equiv_lemma #(`#inttype) (`@x);
//           get_bit_pow2_minus_one #(`#inttype) (`@x_log) (`#nth)
//         ))
//     }] in
//     // fail (term_to_string (quote sv));
//     pack_sigelt sv


// %splice[] (
//   let flatmap #a #b (f: a -> Tac (list b)) l = FStar.List.Tot.flatten (map f l) in
//   flatmap (fun size -> 
//     flatmap (fun x -> 
//       flatmap (fun signed -> 
//         if x <= size - (if signed then 1 else 0)
//         then [gen_get_bit_pow2_minus_one signed size x]
//         else []
//       ) [false; true]
//     ) [1;2;3;4;5;6;7;8]
//   ) [8; 32]
// )



#push-options "--fuel 0 --ifuel 1 --z3rlimit 150"
let bit_vector_lemma (#t1 #t2: inttype)
                     (#len1 #len2: usize)
                     (arr1: t_Array (int_t t1) len1)
                     (arr2: t_Array (int_t t2) len2)
                     (d1: bit_num t1)
                     (d2: bit_num t2)
  : Lemma
    (requires
      (let len = v d1 * v len1 in
        len == v d2 * v len2
      /\ v len1 < max_usize
      /\ v len2 < max_usize
      /\ len < max_usize
      /\ (forall (i: nat). i < len
           ==> get_bit_arr_nat #t1 #(v len1) arr1 (v d1) i 
            == get_bit_arr_nat #t2 #(v len2) arr2 (v d2) i
        )))
     (ensures bit_vector arr1 d1 == bit_vector arr2 d2)
  = assert (bit_vector arr1 d1 `Seq.equal` bit_vector arr2 d2)
#pop-options
