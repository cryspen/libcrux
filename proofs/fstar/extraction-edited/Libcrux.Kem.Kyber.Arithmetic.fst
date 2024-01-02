module Libcrux.Kem.Kyber.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul


let lemma_mul_i32_range (n1 n2:i32) (b1 b2:nat):
  Lemma (requires (i32_range n1 b1 /\ i32_range n2 b2 /\ b1 * b2 < pow2 31))
        (ensures (range (v n1 * v n2) i32_inttype /\
                  i32_range (n1 *! n2) (b1 * b2)))
  = if v n1 = 0 || v n2 = 0 then ()
    else 
    let open FStar.Math.Lemmas in
    lemma_abs_bound (v n1) b1;
    lemma_abs_bound (v n2) b2;
    lemma_abs_mul (v n1) (v n2);
    lemma_mult_le_left (abs (v n1)) (abs (v n2)) b2;
    lemma_mult_le_right b2 (abs (v n1)) b1;
    lemma_abs_bound (v n1 * v n2) (b1 * b2)


let lemma_add_i32_range (n1 n2:i32) (b1 b2:nat):
  Lemma (requires (i32_range n1 b1 /\ i32_range n2 b2 /\ b1 + b2 < pow2 31))
        (ensures (range (v n1 + v n2) i32_inttype /\
                  i32_range (n1 +! n2) (b1 + b2)))
  = ()

let mul_i32_b #b1 #b2 x y = 
  lemma_mul_i32_range x y b1 b2;
  x *! y

let add_i32_b #b1 #b2 x y = 
  lemma_add_i32_range x y b1 b2;
  x +! y

let sub_i32_b #b1 #b2 x y = 
  x -! y

let cast_i32_b #b1 #b2 x =
  x <: i32_b b2

let v_MONTGOMERY_R: i32 = 1l <<! v_MONTGOMERY_SHIFT

let mont_to_spec_fe (m:t_FieldElement) = admit()

#push-options "--fuel 0 --ifuel 0 --z3rlimit 500"
let get_n_least_significant_bits n value = 
  let _:Prims.unit = () <: Prims.unit in
  let res = value &. ((1ul <<! n <: u32) -! 1ul <: u32) in
  logand_mask_lemma value (v n);
  mk_int_equiv_lemma #u32_inttype 1;
  assert ((1ul <<! n) == mk_int (pow2 (v n)));
  assert (res == logand value (mk_int (pow2 (v n)) -! mk_int 1));
  assert (v res == v value % (pow2 (v n)));
  assert (v res < pow2 (v n));
  res
#pop-options 

let barrett_reduce value = 
  let _:Prims.unit = () <: Prims.unit in
  let x : i32 = value in
  let t:i64 =
    ((Core.Convert.f_from x <: i64) *! v_BARRETT_MULTIPLIER <: i64) +!
    (v_BARRETT_R >>! 1l <: i64)
  in
  let quotient:i32 = cast (t >>! v_BARRETT_SHIFT <: i64) <: i32 in
  let result:i32 = value -! (quotient *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) in
  let _:Prims.unit = () <: Prims.unit in
  admit();
  result

let montgomery_reduce value = 
  let _:i32 = v_MONTGOMERY_R in
  let _:Prims.unit = () <: Prims.unit in
  let t:u32 =
    (get_n_least_significant_bits v_MONTGOMERY_SHIFT (cast (value <: i32) <: u32) <: u32) *!
    v_INVERSE_OF_MODULUS_MOD_R
  in
  let k:i16 = cast (get_n_least_significant_bits v_MONTGOMERY_SHIFT t <: u32) <: i16 in
  let k_times_modulus:i32 =
    (cast (k <: i16) <: i32) *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
  in
  let c:i32 = k_times_modulus >>! v_MONTGOMERY_SHIFT in
  let value_high:i32 = value >>! v_MONTGOMERY_SHIFT in
  let res = value_high -! c in
  admit(); // P-F
  res

let montgomery_multiply_sfe_by_fer fe fer =
  montgomery_reduce (mul_i32_b fe fer)


let to_standard_domain mfe =
  montgomery_reduce (mul_i32_b mfe (v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS <: i32_b 1353))

let to_unsigned_representative (fe: i32) =
  let _:Prims.unit = () <: Prims.unit in
  logand_lemma Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS (fe >>! 31l <: i32);
  let res =  
  cast (fe +! (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &. (fe >>! 31l <: i32) <: i32) <: i32)
  <:
  u16
  in
  admit(); //P-F
  res

let derefine_poly_b #b x =
  let r = createi (sz 256) (fun i -> (x.f_coefficients.[i] <: i32)) in
  {f_coefficients = r}

let derefine_vector_b #p #b x =
  let r = createi (p.v_RANK) (fun i -> derefine_poly_b #b x.[i]) in
  r

let derefine_matrix_b #p #b x =
  let r = createi (p.v_RANK) (fun i -> derefine_vector_b #p #b x.[i]) in
  r

let cast_poly_b #b1 #b2 x =
  let r = createi (sz 256) (fun i -> (x.f_coefficients.[i] <: i32_b b2)) in
  let res = {f_coefficients = r} in
  let dx = (derefine_poly_b x).f_coefficients in
  let dr = (derefine_poly_b res).f_coefficients in
  assert (forall (i:usize). v i < 256 ==> 
    (dx.[i] <: i32) == 
    (dr.[i] <: i32));
  assert (forall i. Seq.index dx i == (dx.[sz i] <: i32));
  eq_intro dx dr;
  assert(Seq.equal dx dr);
  res

let add_to_ring_element #b1 #b2 v_K lhs rhs =
  let _:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = () <: Prims.unit in
  let orig_lhs = lhs in
  [@ inline_let]
  let inv = fun (acc:t_PolynomialRingElement_b (b1+b2)) (i:usize) ->
      (forall j. j <. i ==> acc.f_coefficients.[j] == lhs.f_coefficients.[j] +! rhs.f_coefficients.[j]) /\
      (forall j. j >=. i ==> acc.f_coefficients.[j] == orig_lhs.f_coefficients.[j]) in
  let lhs:t_PolynomialRingElement_b (b1 + b2) =
    Rust_primitives.Iterators.foldi_range #_ #(t_PolynomialRingElement_b (b1+b2))  #inv {
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end =
              Core.Slice.impl__len (Rust_primitives.unsize lhs.f_coefficients <: t_Slice (i32_b b1))
            }
      (cast_poly_b #b1 #(b1+b2) lhs)
      (fun lhs i ->
          let lhs:t_PolynomialRingElement_b (b1+b2) = lhs in
          let i:usize = i in
          assert (orig_lhs.f_coefficients.[i] == lhs.f_coefficients.[i]);
          let lhsi: i32_b b1 = orig_lhs.f_coefficients.[i] in
          let lhs = 
          {
            lhs with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs.f_coefficients
              i
              (add_i32_b #b1 #b2 (lhsi) (rhs.f_coefficients.[ i ]))
            <:
            t_Array (i32_b (b1 + b2)) (sz 256)
          }
          <:
          t_PolynomialRingElement_b (b1 + b2)
          in
          assert (forall j. (j >. i /\ j <. sz 256) ==> lhs.f_coefficients.[j] == orig_lhs.f_coefficients.[j]);
          lhs
          )
  in
  let _:Prims.unit = () <: Prims.unit in
  assert (forall j. j <. sz 256 ==> lhs.f_coefficients.[j] == orig_lhs.f_coefficients.[j] +! rhs.f_coefficients.[j]);
  lhs
  
  
 
