module Libcrux.Kem.Kyber.Matrix
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

open Libcrux.Kem.Kyber.Arithmetic

let op_Array_Access (x:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement) (i:usize{v i < 256}): i32  =
    x.f_coefficients.[i]
    

#push-options "--ifuel 0 --z3rlimit 700"
let compute_As_plus_e v_K matrix_A s_as_ntt error_as_ntt =
  let wfZero: wfPolynomialRingElement = (Libcrux.Kem.Kyber.Arithmetic.cast_poly_b #1 #3328 Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO) in
  let result:t_Array wfPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat wfZero v_K
  in
  [@ inline_let]
  let inv0 = fun (acc:t_Array wfPolynomialRingElement v_K) (i:usize) -> 
   (v i <= v v_K) /\
   (forall (j:usize). (v j >= v i /\ v j < v v_K) ==> (acc.[j] <: Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement) == wfZero)
  in
  assert (inv0 result (sz 0));
  let result:t_Array wfPolynomialRingElement v_K =
    Rust_primitives.Iterators.foldi_slice #(t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K) #(t_Array wfPolynomialRingElement v_K) #inv0
      matrix_A
      result
      (fun result temp_1_ ->
          let orig_result = result in
          let orig_result_cast = (cast_vector_b #v_K #3328 #(v v_K * 3328) orig_result) in
          let i, row:(usize & t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K) =
            temp_1_
          in
          [@ inline_let]
          let inv1 = fun (acc:t_Array (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328)) v_K) (inner:usize) ->
             (v inner <= v v_K) /\
             (forall (j:usize). (v j < v i /\ v j < v v_K) ==> acc.[j] == orig_result_cast.[j]) /\
             (forall (j:usize). (v j > v i /\ v j < v v_K) ==> acc.[j] == orig_result_cast.[j]) /\
             (poly_range (acc.[i] <: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328)) (v inner * 3328))
          in
          assert (forall (k:usize). (v k < 256) ==> v (result.[i] <: wfPolynomialRingElement).f_coefficients.[k] == 0);
          assert(inv1 orig_result_cast (sz 0));
          let result:t_Array (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328)) v_K =
            Rust_primitives.Iterators.foldi_slice #Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement #(t_Array (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328)) v_K) #inv1
              row
              orig_result_cast
              (fun result temp_1_ ->
                  let j, matrix_element:(usize &
                    Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement) =
                    temp_1_
                  in
                  let resulti = down_cast_poly_b #(v v_K * 3328) #(v j * 3328) result.[i] in
                  let product:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
                    Libcrux.Kem.Kyber.Ntt.ntt_multiply matrix_element
                      (s_as_ntt.[ j ] <: Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
                  in
                  let product_sum:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b ((v j + 1) * 3328)  =
                      (Libcrux.Kem.Kyber.Arithmetic.add_to_ring_element #(v j * 3328) #3328 v_K
                          resulti
                          product) in
                  let product_sum:(Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328)) = cast_poly_b #((v j+1)* 3328) #(v v_K * 3328) product_sum in 
                  let result:t_Array (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328)) v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                      i
                      product_sum
                  in
                  result)
          in
          let result1 = result in
          [@ inline_let]
          let inv2 = fun (acc:t_Array (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328)) v_K) (inner:usize) -> 
             (v inner <= 256) /\
             (forall (j:usize). (v j < v i /\ v j < v v_K) ==> acc.[j] == orig_result_cast.[j]) /\
             (forall (j:usize). (v j > v i /\ v j < v v_K) ==> acc.[j] == orig_result_cast.[j]) /\
             (forall (j:usize). (v j < v inner) ==> (i32_range (acc.[i] <: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328)).f_coefficients.[j] 3328))
             // And all indexes above v inner are unchanged from result1
          in
          assert (inv2 result1 (sz 0));
          let result:t_Array (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328)) v_K =
            Rust_primitives.Iterators.foldi_range #_ #(t_Array (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328)) v_K) #inv2 {
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            }
            result
            (fun result j -> 
                let result: t_Array (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328)) v_K = result in
                let j:usize = j in
                let resulti:(Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328)) = result.[ i ]  <:  (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328)) in
                let coefficient_normal_form: i32_b ((nat_div_ceil (v v_K * 3328 * 1353) (pow2 16)) + 1665) =
                  Libcrux.Kem.Kyber.Arithmetic.to_standard_domain #(v v_K * 3328) (resulti
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ])
                in
                assert ((nat_div_ceil (v v_K * 3328 * 1353) (pow2 16)) + 1665 <= 1940);
                let coefficient_normal_form: i32_b 1940 = cast_i32_b #((nat_div_ceil (v v_K * 3328 * 1353) (pow2 16)) + 1665)  #1940 coefficient_normal_form in
                let x1: i32_b 3328 = (error_as_ntt.[ i ]
                                  <:
                                  Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
                                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] in
                let x2: i32_b 5268 = add_i32_b coefficient_normal_form x1 in
                assert (5268 <= v v_BARRETT_R /\ v v_BARRETT_R < pow2 31);
                let x3: i32_b (v v_BARRETT_R) = cast_i32_b #5268 #(v v_BARRETT_R) x2 in
                let resultij: i32_b 3328 =  Libcrux.Kem.Kyber.Arithmetic.barrett_reduce x3 in
                let resultij: i32_b (v v_K * 3328) =  cast_i32_b #3328 #(v v_K * 3328) resultij in
                let resulti_coeffs =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                   (resulti.Libcrux.Kem.Kyber.Arithmetic.f_coefficients)
                    j resultij in
                let result = 
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                  i
                  ({
                      resulti with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      = resulti_coeffs
                    }
                    <:
                    Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K*3328)) in
                assert ((result.[i]).f_coefficients.[j] == resultij);
                assert(inv2 result (j +! sz 1));
                let result: x:t_Array (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328)) v_K{inv2 x (j +! mk_int 1)} = result in
                result) in
      assert (v i + 1 < v v_K ==> result.[i +! sz 1] == orig_result_cast.[i +! sz 1]);
      let result: t_Array wfPolynomialRingElement v_K =
        down_cast_vector_b #v_K #(v v_K * 3328) #3328 result in
      assert (forall (j:usize). (v j >= v i + 1 /\ v j < v v_K) ==> derefine_poly_b result.[j] == derefine_poly_b orig_result.[j]); 
      assume (inv0 result (i +! sz 1));
      result)
  in
  admit(); //P-F
  result  
#pop-options 

#push-options "--ifuel 0 --z3rlimit 100"
let compute_message #p v_K m_v secret_as_ntt u_as_ntt = 
  let result:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328) =
    Libcrux.Kem.Kyber.Arithmetic.cast_poly_b Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let acc_t = Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328) in
  [@ inline_let]
  let inv = fun (acc:acc_t) (i:usize) -> 
             (v i <= v v_K) /\
             (poly_range #(v v_K * 3328) acc (v i * 3328))
  in
  let result:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328) =
    Rust_primitives.Iterators.foldi_range #_ #acc_t #inv {
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
      result 
      (fun result i ->
          let i:usize = i in
          let result:t_PolynomialRingElement_b (v i * 3328) = 
            down_cast_poly_b #(v v_K * 3328) #(v i * 3328) result in
          let product:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            Libcrux.Kem.Kyber.Ntt.ntt_multiply (secret_as_ntt.[ i ]
                <:
                Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
              (u_as_ntt.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
          in
          let result:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b ((v i+1) * 3328)  =
            Libcrux.Kem.Kyber.Arithmetic.add_to_ring_element v_K result product
          in
          let result = cast_poly_b #((v i + 1) * 3328) #(v v_K * 3328) result in
          assert(inv result (i +! sz 1));
          result)
  in
  let acc_t = t_PolynomialRingElement_b (64*v v_K*3328) in
  let result:acc_t = Libcrux.Kem.Kyber.Ntt.invert_ntt_montgomery v_K result
  in
  [@ inline_let]
  let inv = fun (acc:acc_t) (i:usize) ->
    (v i <= 256) /\
    (forall (j:usize). (v j < v i) ==> i32_range ((acc <: t_PolynomialRingElement_b (64* v v_K * 3328)).f_coefficients.[j]) 3328) in
  let result:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (64*v v_K*3328) =
    Rust_primitives.Iterators.foldi_range #_ #_ #inv {
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            }
      result 
      (fun result i ->
          let i:usize = i in
          let coefficient_normal_form: i32_b (nat_div_ceil (306921472*v v_K) 65536 + 1665) = 
              Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce 
                           (Libcrux.Kem.Kyber.Arithmetic.mul_i32_b #(64 * v v_K * 3328) #1441
                           result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ] 
                           (1441l <: Libcrux.Kem.Kyber.Arithmetic.i32_b 1441)) in
          let resulti : i32_b 3328 = (Libcrux.Kem.Kyber.Arithmetic.barrett_reduce ((m_v
                          .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                        <:
                        i32) -!
                      coefficient_normal_form
                      <:
                      i32)
                  <:
                  i32) in
          let resulti = cast_i32_b #3328 #(64*v v_K*3328) resulti in
          let result =
            {
              result with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                i resulti
            }
          in
          assert (inv result (i +! sz 1));
          result)
  in
  admit(); //P-F
  result
#pop-options

#push-options "--ifuel 0 --z3rlimit 100"
let compute_ring_element_v v_K tt_as_ntt r_as_ntt error_2_ message =
  let result:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328) =
    Libcrux.Kem.Kyber.Arithmetic.cast_poly_b Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  [@ inline_let]
  let inv = fun (acc:t_PolynomialRingElement_b (v v_K * 3328)) (i:usize) ->
    (v i <= 256) /\
    (poly_range acc (v i * 3328)) in
  let result:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328) =
    Rust_primitives.Iterators.foldi_range #_ #_ #inv ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
        <:
        Core.Ops.Range.t_Range usize)
      result
      (fun result i ->
          let product:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
            Libcrux.Kem.Kyber.Ntt.ntt_multiply (tt_as_ntt.[ i ]
                <:
                Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
              (r_as_ntt.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
          in
          let result:t_PolynomialRingElement_b (v i * 3328) = 
            down_cast_poly_b #(v v_K * 3328) #(v i * 3328) result in
          let result:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b ((v i + 1) * 3328) =
            Libcrux.Kem.Kyber.Arithmetic.add_to_ring_element v_K result product
          in
          cast_poly_b result)
  in
  let result:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (64 * v v_K * 3328) =
    Libcrux.Kem.Kyber.Ntt.invert_ntt_montgomery v_K result
  in
  [@ inline_let]
  let inv = fun (acc:t_PolynomialRingElement_b (64 * v v_K * 3328)) (i:usize) -> 
    (v i <= 256) /\
    (forall (j:usize). (v j < v i) ==> i32_range ((acc <: t_PolynomialRingElement_b (64* v v_K * 3328)).f_coefficients.[j]) 3328) in
  let result:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (64 * v v_K * 3328) =
    Rust_primitives.Iterators.foldi_range #_ #_ #inv {
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            }
      result 
      (fun result i ->
          let coefficient_normal_form: i32_b (nat_div_ceil (306921472*v v_K) 65536 + 1665) = 
              Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce 
                           (Libcrux.Kem.Kyber.Arithmetic.mul_i32_b #(64 * v v_K * 3328) #1441
                           result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ] 
                           (1441l <: Libcrux.Kem.Kyber.Arithmetic.i32_b 1441)) in
          let resulti : i32_b 3328 = 
            (Libcrux.Kem.Kyber.Arithmetic.barrett_reduce ((coefficient_normal_form +!
                        (error_2_.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ] <: i32)
                        <:
                        i32) +!
                      (message.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ] <: i32)
                      <:
                      i32)
                  <:
                  i32) in
          let resulti = cast_i32_b #3328 #(64*v v_K*3328) resulti in
          let result =
            {
              result with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                i resulti
            }
          in
          result)
  in
  admit(); //P-F
  result
#pop-options

#push-options "--ifuel 0 --z3rlimit 300"
let compute_vector_u
      (v_K: usize)
      (a_as_ntt: t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K) v_K)
      (r_as_ntt error_1_: t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K) =
  let wfZero: wfPolynomialRingElement = (Libcrux.Kem.Kyber.Arithmetic.cast_poly_b #1 #3328 Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO) in
  let result:t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat wfZero v_K
  in
  let acc_t = t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K in
  [@ inline_let]
  let inv0 = fun (acc:t_Array wfPolynomialRingElement v_K) (i:usize) -> 
   (v i <= v v_K) /\
   (forall (j:usize). (v j >= v i /\ v j < v v_K) ==> (acc.[j] <: Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement) == wfZero)
  in
  let result:t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K =
    Rust_primitives.Iterators.foldi_slice #(t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K) #acc_t #inv0
      a_as_ntt
      result
      (fun result temp_1_ ->
          let result:t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K = result in
          let orig_result = result in
          let orig_result_cast = (cast_vector_b #v_K #3328 #(64 * v v_K * 3328) orig_result) in
          let i, row:(usize & t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K) =
            temp_1_
          in
          [@ inline_let]
          let inv1 = fun (acc:t_Array (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (64 * v v_K * 3328)) v_K) (inner:usize) ->
             (v inner <= v v_K) /\
             (forall (j:usize). (v j < v i /\ v j < v v_K) ==> acc.[j] == orig_result_cast.[j]) /\
             (forall (j:usize). (v j > v i /\ v j < v v_K) ==> acc.[j] == orig_result_cast.[j]) /\
             (poly_range (acc.[i] <: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (64 * v v_K * 3328)) (v inner * 3328))
          in
          assert (forall (k:usize). (v k < 256) ==> v (result.[i] <: wfPolynomialRingElement).f_coefficients.[k] == 0);
          assert(inv1 orig_result_cast (sz 0));
          let result:t_Array (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (64 * v v_K * 3328)) v_K =
            Rust_primitives.Iterators.foldi_slice #Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement #(t_Array (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (64 * v v_K * 3328)) v_K) #inv1
              row
              orig_result_cast
              (fun result temp_1_ ->
                  let j, a_element:(usize & Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement) =
                    temp_1_
                  in
                  let resulti = down_cast_poly_b #(64 * v v_K * 3328) #(v j * 3328) result.[i] in
                  let product:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
                    Libcrux.Kem.Kyber.Ntt.ntt_multiply a_element
                      (r_as_ntt.[ j ] <: Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
                  in
                  let product_sum:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b ((v j + 1) * 3328)  =
                      (Libcrux.Kem.Kyber.Arithmetic.add_to_ring_element #(v j * 3328) #3328 v_K
                          resulti
                          product) in
                  let product_sum:(Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (64 * v v_K * 3328)) = cast_poly_b #((v j+1)* 3328) #(64 * v v_K * 3328) product_sum in 
                  let result:t_Array (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (64 * v v_K * 3328)) v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                      i
                      product_sum
                  in
                  result)
          in
          assert (forall (j:usize). (v j < v i /\ v j < v v_K) ==> result.[j] == orig_result_cast.[j]);
          assert (forall (j:usize). (v j > v i /\ v j < v v_K) ==> result.[j] == orig_result_cast.[j]);
          let resulti : t_PolynomialRingElement_b (v v_K * 3328) = down_cast_poly_b result.[i] in
          let result =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
              i
              (Libcrux.Kem.Kyber.Ntt.invert_ntt_montgomery v_K resulti)
           in
          [@ inline_let]
          let inv2 = fun (acc:t_Array (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (64*v v_K * 3328)) v_K) (inner:usize) -> 
             (v inner <= 256) /\
             (forall (j:usize). (v j < v i /\ v j < v v_K) ==> acc.[j] == orig_result_cast.[j]) /\
             (forall (j:usize). (v j > v i /\ v j < v v_K) ==> acc.[j] == orig_result_cast.[j]) /\
             (forall (j:usize). (v j < v inner) ==> (i32_range (acc.[i] <: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (64*v v_K * 3328)).f_coefficients.[j] 3328))
             // And all indexes above v inner are unchanged from result1
          in
          assert (forall (j:usize). (v j < v i /\ v j < v v_K) ==> result.[j] == orig_result_cast.[j]);
          assert (forall (j:usize). (v j > v i /\ v j < v v_K) ==> result.[j] == orig_result_cast.[j]);
          assert (inv2 result (sz 0));
          let result:t_Array (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (64*v v_K * 3328)) v_K =
            Rust_primitives.Iterators.foldi_range #_ #(t_Array (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (64*v v_K * 3328)) v_K) #inv2 {
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            }
            result
            (fun result j ->
                let result: t_Array (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (64*v v_K * 3328)) v_K = result in
                let resulti:(Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (64*v v_K * 3328)) = result.[ i ]  <:  (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (64*v v_K * 3328)) in
                let coefficient_normal_form: i32_b (nat_div_ceil (306921472*v v_K) 65536 + 1665) = 
              Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce 
                           (Libcrux.Kem.Kyber.Arithmetic.mul_i32_b #(64 * v v_K * 3328) #1441
                           (resulti <: t_PolynomialRingElement_b (64*v v_K * 3328)).f_coefficients.[j] (1441l <: Libcrux.Kem.Kyber.Arithmetic.i32_b 1441)) in
                let resultij: i32_b 3328 = (Libcrux.Kem.Kyber.Arithmetic.barrett_reduce 
                                    (add_i32_b coefficient_normal_form ((error_1_.[ i ]
                                    <:
                                    Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
                                    .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ]))) in
                let result =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                    i
                    ({
                        resulti with
                        Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        =
                        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (resulti
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients)
                          j
                          (cast_i32_b #3328 #(64 * v v_K * 3328) resultij)
                      }) in
                result)
        in
        let result: t_Array wfPolynomialRingElement v_K =
          down_cast_vector_b #v_K #(64 * v v_K * 3328) #3328 result in
        assert (forall (j:usize). (v j >= v i + 1 /\ v j < v v_K) ==> derefine_poly_b result.[j] == derefine_poly_b orig_result.[j]); 
        assume (inv0 result (i +! sz 1));
        result)
  in
  admit(); //P-F
  result
#pop-options

let sample_matrix_A (v_K: usize) (seed: t_Array u8 (sz 34)) (transpose: bool) =
  let wfZero: wfPolynomialRingElement = (Libcrux.Kem.Kyber.Arithmetic.cast_poly_b #1 #3328 Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO) in
  let v_A_transpose:t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat wfZero v_K) v_K
  in
  let v_A_transpose:t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K) v_K =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v_A_transpose
      (fun v_A_transpose i ->
          let v_A_transpose:t_Array
            (t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K) v_K =
            v_A_transpose
          in
          let i:usize = i in
          let seeds:t_Array (t_Array u8 (sz 34)) v_K = Rust_primitives.Hax.repeat seed v_K in
          let seeds:t_Array (t_Array u8 (sz 34)) v_K =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = sz 0;
                      Core.Ops.Range.f_end = v_K
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                Core.Ops.Range.t_Range usize)
              seeds
              (fun seeds j ->
                  let seeds:t_Array (t_Array u8 (sz 34)) v_K = seeds in
                  let j:usize = j in
                  let seeds:t_Array (t_Array u8 (sz 34)) v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seeds
                      j
                      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (seeds.[ j ]
                            <:
                            t_Array u8 (sz 34))
                          (sz 32)
                          (cast (i <: usize) <: u8)
                        <:
                        t_Array u8 (sz 34))
                  in
                  let seeds:t_Array (t_Array u8 (sz 34)) v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seeds
                      j
                      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (seeds.[ j ]
                            <:
                            t_Array u8 (sz 34))
                          (sz 33)
                          (cast (j <: usize) <: u8)
                        <:
                        t_Array u8 (sz 34))
                  in
                  seeds)
          in
          let xof_bytes:t_Array (t_Array u8 (sz 840)) v_K =
            Libcrux.Kem.Kyber.Hash_functions.v_XOFx4 v_K seeds
          in
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                    Core.Ops.Range.f_start = sz 0;
                    Core.Ops.Range.f_end = v_K
                  }
                  <:
                  Core.Ops.Range.t_Range usize)
              <:
              Core.Ops.Range.t_Range usize)
            v_A_transpose
            (fun v_A_transpose j ->
                let v_A_transpose:t_Array
                  (t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K) v_K =
                  v_A_transpose
                in
                let j:usize = j in
                let sampled:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
                  Libcrux.Kem.Kyber.Sampling.sample_from_uniform_distribution (xof_bytes.[ j ]
                      <:
                      t_Array u8 (sz 840))
                in
                if transpose
                then
                  let v_A_transpose:t_Array
                    (t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K) v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A_transpose
                      j
                      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A_transpose.[ j
                            ]
                            <:
                            t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K)
                          i
                          sampled
                        <:
                        t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K)
                  in
                  v_A_transpose
                else
                  let v_A_transpose:t_Array
                    (t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K) v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A_transpose
                      i
                      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A_transpose.[ i
                            ]
                            <:
                            t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K)
                          j
                          sampled
                        <:
                        t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K)
                  in
                  v_A_transpose))
  in
  admit(); //P-F
  v_A_transpose
