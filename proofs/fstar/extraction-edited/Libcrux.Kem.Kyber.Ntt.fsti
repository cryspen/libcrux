module Libcrux.Kem.Kyber.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul
open Libcrux.Kem.Kyber.Arithmetic

val v_ZETAS_TIMES_MONTGOMERY_R: x:t_Array (i32_b 1664) (sz 128){v (x.[sz 1] <: i32) == -758}

val ntt_multiply_binomials (a:wfFieldElement&wfFieldElement) (b: wfFieldElement&wfFieldElement) (zeta: i32_b 1664) :
    Pure (wfFieldElement & wfFieldElement)
    (requires True)
    (ensures (fun _ -> True))

val invert_ntt_at_layer (#v_K:usize{v v_K >= 1 /\ v v_K <= 4})
      (#b:nat{b <= v v_K * 3328 * 64})
      (zeta_i: usize{v zeta_i >= 1 /\ v zeta_i <= 128})
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b b)
      (layer: usize{v layer > 0 /\ 
                    v layer <= 7 /\ 
                    v zeta_i == pow2 (8 - v layer) /\ 
                    b == v v_K * 3328 * pow2(v layer - 1)})
    : Prims.Pure (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (2*b))
      Prims.l_True
      (fun x -> let (zeta_fin,re) = x in v zeta_fin == pow2 (7 - v layer))

val invert_ntt_montgomery (v_K: usize{v v_K >= 1 /\ v v_K <= 4}) 
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328))
    : Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (64 * v v_K * 3328)

val ntt_at_layer 
      (#b:nat{b <= 31175})
      (zeta_i: usize{v zeta_i < 128})
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b b)
      (layer: usize{v layer > 0 /\ 
                    v layer <= 7 /\ 
                    v zeta_i == pow2 (7 - v layer) - 1})
      (initial_coefficient_bound: usize{b == (7 - v layer) * 3328 + v initial_coefficient_bound})
    : Pure (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (3328+b))
      (requires True)
      (ensures fun (zeta_i, result) -> v zeta_i == pow2 (8 - v layer) - 1)

val ntt_at_layer_3_ (#b:nat)
      (zeta_i: usize{v zeta_i < 128})
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b b)
      (layer: usize{v layer > 0 /\ 
                    v layer <= 6 /\ 
                    v zeta_i == pow2 (7 - v layer) - 1 /\
                    b == (6 - v layer) * 3328 + 11207})
    : Prims.Pure (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (3328+b))
      Prims.l_True
      (ensures fun (zeta_i,result) -> v zeta_i == pow2 (8 - v layer) - 1)

val ntt_at_layer_3328_ (#b:nat{b <= 7*3328})
      (zeta_i: usize{v zeta_i < 128})
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b b)
      (layer: usize{v layer > 0 /\ 
                    v layer <= 7 /\ 
                    v zeta_i == pow2 (7 - v layer) - 1  /\
                    b == (7 - v layer) * 3328 + 3328})
    : Prims.Pure (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (3328+b))
      Prims.l_True
      (ensures fun (zeta_i,result) -> v zeta_i == pow2 (8 - v layer) - 1)

val ntt_binomially_sampled_ring_element (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 7)
    : Prims.Pure (Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
      (requires True)
      (ensures (fun _ -> True))

val ntt_multiply (lhs: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3328)
                 (rhs: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3328)
    : Prims.Pure (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3328)
      (requires True)
      (ensures (fun _ -> True))
    
val ntt_vector_u
      (v_VECTOR_U_COMPRESSION_FACTOR: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3328)
    : Prims.Pure (Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
      (requires True)
      (ensures fun _ -> True)

