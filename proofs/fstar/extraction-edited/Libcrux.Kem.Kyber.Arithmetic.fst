module Libcrux.Kem.Kyber.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul


let lemma_mul_i32_range (n1 n2: i32) (b1 b2: nat)
    : Lemma (requires (i32_range n1 b1 /\ i32_range n2 b2 /\ b1 * b2 < pow2 31))
      (ensures (range (v n1 * v n2) i32_inttype /\ i32_range (n1 *! n2) (b1 * b2))) =
  if v n1 = 0 || v n2 = 0
  then ()
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

#push-options "--ifuel 0 --z3rlimit 250"
let shr_i32_b #b #t x y =
  let r = (x <: i32) >>! y in
  assert (v r == v x / pow2 (v y));
  Math.Lemmas.lemma_div_le (v x) b (pow2 (v y));
  assert (v x / (pow2 (v y)) <= b / (pow2 (v y)));
  Math.Lemmas.lemma_div_le (-b) (v x) (pow2 (v y));
  assert (v x / (pow2 (v y)) >= (-b) / (pow2 (v y)));
  if (b % pow2 (v y) = 0)  
  then (Math.Lemmas.div_exact_r b (pow2 (v y));
        assert (b = (b/pow2 (v y)) * pow2 (v y));
        assert (-b = -((b/pow2 (v y)) * pow2 (v y)));
        Math.Lemmas.neg_mul_left (b/pow2 (v y)) (pow2 (v y));
        assert (-b = (-(b/pow2 (v y))) * pow2 (v y));
        assert ((-b)/pow2(v y) = ((-(b/pow2 (v y))) * pow2 (v y)) / pow2 (v y));
        Math.Lemmas.cancel_mul_div (-(b/pow2 (v y))) (pow2 (v y));
        assert ((-b)/pow2(v y) = -(b/pow2 (v y)));
        assert (nat_div_ceil b (pow2 (v y)) == b / pow2 (v y));
        assert (i32_range r (b / pow2 ( v y)));
        r <: i32_b (nat_div_ceil b (pow2 (v y))))
  else (let rem = b % pow2 (v y) in
        let quo = b / pow2 (v y) in
        Math.Lemmas.lemma_div_mod b (pow2 (v y));        
        assert (b = quo * pow2 (v y) + rem);
        assert (-b = -(quo * pow2 (v y)) - rem);
        Math.Lemmas.neg_mul_left quo (pow2 (v y));
        assert (-b = (-quo) * pow2 (v y) - rem);
        assert ((-b)/pow2(v y) = (-rem + (-quo) * pow2 (v y))/pow2 (v y));
        Math.Lemmas.division_addition_lemma (-rem) (pow2 (v y)) (-quo);
        assert ((-b)/pow2(v y) = ((-rem)/pow2 (v y) -quo));
        Math.Lemmas.division_definition (-rem) (pow2 (v y)) (-1);
        assert ((-rem)/pow2 (v y) == -1);
        assert ((-b)/pow2(v y) = -1 -quo);
        assert ((-b)/pow2(v y) = (-quo - 1));
        assert ((-b)/pow2(v y) = -(quo + 1));
        assert (nat_div_ceil b (pow2 (v y)) == quo + 1);
        assert (i32_range r (quo+1));
        r <: i32_b (nat_div_ceil b (pow2 (v y))))
#pop-options

let v_BARRETT_R: i64 =
  let result = 1L <<! v_BARRETT_SHIFT in
  assert_norm (result == mk_int (67108864 @%. Lib.IntTypes.S64));
  result

let v_MONTGOMERY_R =
  let result: i32 = 1l <<! v_MONTGOMERY_SHIFT in
  assert_norm (result == mk_int (65536 @%. Lib.IntTypes.S32));
  result

let v_MONTGOMERY_R_INV = 
  assert_norm((v 169l * pow2 16) % 3329 == 1);
  169l
  
#push-options "--fuel 0 --ifuel 1 --z3rlimit 100 --split_queries always"
let get_n_least_significant_bits n value = 
  let _:Prims.unit = () <: Prims.unit in
  let res = value &. ((1ul <<! n <: u32) -! 1ul <: u32) in
  calc (==) {
    v res;
    (==) { }
    v (logand value ((1ul <<! n) -! 1ul));
    (==) {mk_int_equiv_lemma #u32_inttype 1} 
    v (logand value (((mk_int 1) <<! n) -! (mk_int 1)));
    (==) { }
    v (logand value (mk_int ((1 * pow2 (v n)) % pow2 32) -! (mk_int 1)));
    (==) {Math.Lemmas.small_mod (pow2 (v n)) (pow2 32); Math.Lemmas.pow2_lt_compat 32 (v n)}
    v (logand value ((mk_int (pow2 (v n))) -! (mk_int 1)));
    (==) {Math.Lemmas.pow2_lt_compat 32 (v n); logand_mask_lemma value (v n)}
    v value % (pow2 (v n));
  };
  assert (v res < pow2 (v n));
  res
#pop-options 

#push-options "--z3rlimit 250"
let barrett_reduce value = 
  let _:Prims.unit = () <: Prims.unit in
  let x : i32 = value in
  let t:i64 =
    ((Core.Convert.f_from x <: i64) *! v_BARRETT_MULTIPLIER <: i64) +!
    (v_BARRETT_R >>! 1l <: i64)
  in
  assert_norm (v v_BARRETT_MULTIPLIER == (pow2 27 + 3329) / (2*3329));
  assert (v t = v x * v v_BARRETT_MULTIPLIER + pow2 25);
  let quotient:i32 = cast (t >>! v_BARRETT_SHIFT <: i64) <: i32 in
  assert (v quotient = v t / pow2 26);
  let result:i32 = value -! (quotient *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) in
  calc (==) {
    v result % 3329;
    (==) { }
    (v value - (v quotient * 3329)) % 3329;
    (==) {Math.Lemmas.lemma_mod_sub_distr (v value) (v quotient * 3329) 3329}
    (v value - (v quotient * 3329) % 3329) % 3329;
    (==) {Math.Lemmas.cancel_mul_mod (v quotient) 3329}
    (v value - 0) % 3329;    
    (==) {}
    (v value) % 3329;    
  };
  result
#pop-options 

#push-options "--ifuel 0 --z3rlimit 1600"
let montgomery_reduce #b value = 
  let _:i32 = v_MONTGOMERY_R in
  let _:Prims.unit = () <: Prims.unit in
  let v0 = (cast (value <: i32) <: u32) in
  assert (v v0 == v value % pow2 32);
  let t0 = (get_n_least_significant_bits v_MONTGOMERY_SHIFT v0 <: u32) in
  assert (v t0 = (v value % pow2 32) % pow2 16);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v value) 16 32;
  assert (v t0 = v value % pow2 16);
  let t:u32 =
    t0 *!
    v_INVERSE_OF_MODULUS_MOD_R
  in
  assert (v t = (v value % pow2 16) * v v_INVERSE_OF_MODULUS_MOD_R);
  let k0 = get_n_least_significant_bits v_MONTGOMERY_SHIFT t <: u32 in
  let k:i32_b (pow2 15) = cast (cast k0 <: i16) <: i32 in
  calc (==) {
    v k % pow2 16;
    == { }
    v k0 % pow2 16;
    == { }
    v t % pow2 16;
    == { }
    ((v value % pow2 16) * v v_INVERSE_OF_MODULUS_MOD_R) % pow2 16;
    == {Math.Lemmas.lemma_mod_mul_distr_l (v value) (v v_INVERSE_OF_MODULUS_MOD_R) (pow2 16)}
    (v value * v v_INVERSE_OF_MODULUS_MOD_R) % pow2 16;
  };
  assert_norm((62209 * 3329) % pow2 16 == 1);
  assert((v v_INVERSE_OF_MODULUS_MOD_R * 3329) % pow2 16 == 1);
  calc (==) {
    (v k * 3329) % pow2 16;
    == {Math.Lemmas.lemma_mod_mul_distr_l (v k) 3329 (pow2 16)}
    ((v k % pow2 16) * 3329) % pow2 16;
    == { }
    ((v value * v v_INVERSE_OF_MODULUS_MOD_R) % pow2 16 * 3329) % pow2 16;
    == {Math.Lemmas.lemma_mod_mul_distr_l (v value * v v_INVERSE_OF_MODULUS_MOD_R) (3329) (pow2 16)}
    (v value * v v_INVERSE_OF_MODULUS_MOD_R * 3329) % pow2 16;   
    == {Math.Lemmas.paren_mul_right (v value) (v v_INVERSE_OF_MODULUS_MOD_R) 3329}
    (v value * (v v_INVERSE_OF_MODULUS_MOD_R * 3329)) % pow2 16;   
    == {Math.Lemmas.lemma_mod_mul_distr_r (v value) (v v_INVERSE_OF_MODULUS_MOD_R * 3329) (pow2 16)}
    (v value * ((v v_INVERSE_OF_MODULUS_MOD_R * 3329) % pow2 16)) % pow2 16;   
    == {Math.Lemmas.mul_one_right_is_same (v value)}
    (v value) % pow2 16;   
  };
  Math.Lemmas.modulo_add (pow2 16) (- (v k * 3329)) (v value) (v k * 3329);
  assert ((v value - v k * 3329) % pow2 16 == (v k * 3329 - v k * 3329) % pow2 16);
  assert ((v value - v k * 3329) % v v_MONTGOMERY_R == 0);
  let k_times_modulus:i32_b (pow2 15 * 3329) =
      mul_i32_b k Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
  in
  let c:i32_b 1665 = shr_i32_b k_times_modulus v_MONTGOMERY_SHIFT in
  let value_high:i32_b (nat_div_ceil b (v v_MONTGOMERY_R)) = shr_i32_b value v_MONTGOMERY_SHIFT in
  assert (v value_high = v value / v v_MONTGOMERY_R);
  let res: i32_b (nat_div_ceil b (v v_MONTGOMERY_R) + 1665) = sub_i32_b value_high c in
  calc (==) {
    v res;
    == { }
    (v value_high - v c);
    == { }
    ((v value / v v_MONTGOMERY_R) - ((v k * 3329) / v v_MONTGOMERY_R));
    == {Math.Lemmas.lemma_div_exact (v value - v k * 3329) (v v_MONTGOMERY_R)}
    ((v value - (v k * 3329)) / v v_MONTGOMERY_R);
  };
  calc (==) {
    v res % 3329;
    == {Math.Lemmas.lemma_div_exact (v value - v k * 3329) (v v_MONTGOMERY_R)}
    (((v value - (v k * 3329)) / v v_MONTGOMERY_R) * ((v v_MONTGOMERY_R * v v_MONTGOMERY_R_INV) % 3329)) % 3329 ;
    == {Math.Lemmas.lemma_mod_mul_distr_r ((v value - (v k * 3329)) / v v_MONTGOMERY_R) (v v_MONTGOMERY_R * v v_MONTGOMERY_R_INV) 3329}
    (((v value - (v k * 3329)) / v v_MONTGOMERY_R) * (v v_MONTGOMERY_R * v v_MONTGOMERY_R_INV)) % 3329 ;
    == {Math.Lemmas.paren_mul_right ((v value - (v k * 3329)) / v v_MONTGOMERY_R) (v v_MONTGOMERY_R) (v v_MONTGOMERY_R_INV)}
    ((((v value - (v k * 3329)) / v v_MONTGOMERY_R) * v v_MONTGOMERY_R) * v v_MONTGOMERY_R_INV) % 3329 ;
    == {Math.Lemmas.lemma_div_exact (v value - v k * 3329) (v v_MONTGOMERY_R)}
    ((v value - (v k * 3329)) * v v_MONTGOMERY_R_INV) % 3329 ;
    == { }
    ((v value * v v_MONTGOMERY_R_INV) - ((v k * 3329) * v v_MONTGOMERY_R_INV)) % 3329 ;
    == {Math.Lemmas.paren_mul_right (v k) 3329 (v v_MONTGOMERY_R_INV)} 
    ((v value * v v_MONTGOMERY_R_INV) - (v k * (3329 * v v_MONTGOMERY_R_INV))) % 3329 ;
    == {Math.Lemmas.swap_mul 3329 (v v_MONTGOMERY_R_INV)} 
    ((v value * v v_MONTGOMERY_R_INV) - (v k * (v v_MONTGOMERY_R_INV * 3329))) % 3329 ;
    == {Math.Lemmas.paren_mul_right (v k) (v v_MONTGOMERY_R_INV) 3329} 
    ((v value * v v_MONTGOMERY_R_INV) - ((v k * v v_MONTGOMERY_R_INV) * 3329)) % 3329 ;
    == {Math.Lemmas.lemma_mod_sub (v value * v v_MONTGOMERY_R_INV) 3329 (v k * v v_MONTGOMERY_R_INV)}
    (v value * v v_MONTGOMERY_R_INV) % 3329 ;
  };
  res
#pop-options

let montgomery_multiply_sfe_by_fer fe fer =
  montgomery_reduce (mul_i32_b fe fer)


let to_standard_domain mfe =
  montgomery_reduce (mul_i32_b mfe (v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS <: i32_b 1353))

let to_unsigned_representative fe =
  let _:Prims.unit = () <: Prims.unit in
  logand_lemma Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS (fe >>! 31l <: i32);
  let res =  
  cast (fe +! (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &. (fe >>! 31l <: i32) <: i32) <: i32) <: u16
  in
  assert (v fe < 0 ==> (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &. (fe >>! 31l <: i32) <: i32) == 3329l);
  assert (v fe >= 0 ==> (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &. (fe >>! 31l <: i32) <: i32) == 0l);
  assert (v fe + 3329 < pow2 16);
  assert (v fe >= -3328);
  assert (v fe < 0 ==> v fe + 3329 >= 0);
  assert (v fe < 0 ==> v res == (v fe + 3329) % pow2 16);
  Math.Lemmas.small_mod (v fe + 3329) (pow2 16);
  assert (v fe < 0 ==> v res == v fe + 3329);
  assert (v fe >= 0 ==> v res == v fe);
  res <: int_t_d u16_inttype 12

let derefine_poly_b #b x =
  let r = createi (sz 256) (fun i -> (x.f_coefficients.[i] <: i32)) in
  {f_coefficients = r}

let derefine_vector_b #v_K #b x =
  let r = createi v_K (fun i -> derefine_poly_b #b x.[i]) in
  r

let derefine_matrix_b #v_K #b x =
  let r = createi v_K (fun i -> derefine_vector_b #v_K #b x.[i]) in
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

let cast_vector_b #v_K #b1 #b2 x =
  let r = createi v_K (fun i -> cast_poly_b #b1 #b2 x.[i]) in
  let dx = derefine_vector_b x in
  let dr = derefine_vector_b r in
  assert (forall (i:usize). v i < v v_K ==>
    dx.[i] == dr.[i]);
  assert (forall i. Seq.index dx i == dx.[sz i]);
  assert (forall i. Seq.index dr i == dr.[sz i]);
  eq_intro dx dr;
  r

let down_cast_poly_b #b1 #b2 x =
  let r = createi (sz 256) 
      (fun i -> 
        let xi:i32_b b2 = x.f_coefficients.[i] in
        xi) in
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

let down_cast_vector_b #v_K #b1 #b2 x =
  let r = createi (v_K) 
      (fun i -> down_cast_poly_b #b1 #b2 x.[i]) in
  let dx = derefine_vector_b x in
  let dr = derefine_vector_b r in
  assert (forall (i:usize). v i < v v_K ==> 
    dx.[i] == dr.[i]);
  assert (forall i. Seq.index dx i == dx.[sz i]);
  assert (forall i. Seq.index dr i == dr.[sz i]);
  eq_intro dx dr;
  assert(Seq.equal dx dr);
  r


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
  
  
 
