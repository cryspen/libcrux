module Libcrux.Kem.Kyber.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let pow2_31 = 2147483648
let i32_range (n:i32) (b:nat) =
  b < pow2_31 /\ v n <= b /\ v n >= -b

type i32_b b = x:i32{i32_range x b}
let nat_div_ceil (x:nat) (y:pos) : nat = if (x % y = 0) then x/y else (x/y)+1

val mul_i32_b (#b1:nat) (#b2:nat{b1 * b2 < pow2_31}) (x:i32_b b1) (y: i32_b b2): r:i32_b (b1 * b2){v r == v x * v y}
val add_i32_b (#b1:nat) (#b2:nat{b1 + b2 < pow2_31}) (x:i32_b b1) (y: i32_b b2): 
  Pure (i32_b (b1 + b2))
  (requires True)
  (ensures fun r -> v r == v x + v y)
val sub_i32_b (#b1:nat) (#b2:nat{b1 + b2 < pow2_31}) (x:i32_b b1) (y: i32_b b2): r:i32_b (b1 + b2){v r == v x - v y}
val cast_i32_b (#b1:nat) (#b2:nat{b1 <= b2 /\ b2 < pow2_31}) (x:i32_b b1): r:i32_b b2{v r == v x}
val shr_i32_b (#b:nat) (#t:inttype) (x:i32_b b) (y:int_t t{v y>0 /\ v y<32}): r:i32_b (nat_div_ceil b (pow2 (v y)))

unfold
let t_FieldElement = i32

unfold
let t_FieldElement_b b = i32_b b

unfold
let wfFieldElement = t_FieldElement_b 3328

unfold
let t_FieldElementTimesMontgomeryR = i32

unfold
let t_MontgomeryFieldElement = i32

let v_BARRETT_MULTIPLIER: i64 = 20159L

let v_BARRETT_SHIFT: i64 = 26L

val v_BARRETT_R: x:i64{v x = pow2 26 /\ x = 67108864L}

let v_INVERSE_OF_MODULUS_MOD_R: u32 = 62209ul

let v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i32 = 1353l

let v_MONTGOMERY_SHIFT: u8 = 16uy

val v_MONTGOMERY_R: x:i32{v x = pow2 16 /\ x = 65536l}

val v_MONTGOMERY_R_INV: x:i32{v x >= 0 /\ v x < 3329 /\ (v x * v v_MONTGOMERY_R) % 3329 == 1 /\ x = 169l}

let int_to_spec_fe (m:int) : Spec.Kyber.field_element = 
    let m_v = m % v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS in
    assert (m_v > -  v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS);
    if m_v < 0 then
      m_v + v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
    else m_v

let wf_fe_to_spec_fe (m: wfFieldElement): Spec.Kyber.field_element =
  if v m < 0
  then v m + v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
  else v m

let to_spec_fe (m:i32) : Spec.Kyber.field_element = 
    int_to_spec_fe (v m)

let to_spec_fe_b #b (m:i32_b b) : Spec.Kyber.field_element = to_spec_fe m

let mont_to_spec_fe (m:t_FieldElement) : Spec.Kyber.field_element =
    int_to_spec_fe (v m * v v_MONTGOMERY_R_INV)

val get_n_least_significant_bits (n: u8 {v n > 0 /\ v n < 32}) (value: u32)
    : Prims.Pure (int_t_d u32_inttype (v n))
      (requires v n < 32)
      (ensures
        fun result ->
          let result:u32 = result in
          v result = v value % pow2 (v n))

//let barrett_pre (value:i32) = 
//    v value <= v v_BARRETT_R /\ v value >= - v v_BARRETT_R
// Appears to work up to +/- 2^28, but not at +/- 2^29

let barrett_post (value:i32) (result:i32) = 
    v result % v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS =
    v value % v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS

val barrett_reduce (value: i32_b (v v_BARRETT_R))
    : Prims.Pure wfFieldElement
    (requires True)
    (ensures fun r -> barrett_post value r)

let montgomery_post (value:i32) (result:i32) =
    v result % v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS =
    (v value * v v_MONTGOMERY_R_INV) % v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS


val montgomery_reduce #b (value: i32_b b)
    : Prims.Pure (i32_b (nat_div_ceil b (v v_MONTGOMERY_R) + 1665))
      (requires True)
      (ensures
        fun result ->
          let result:i32 = result in
          montgomery_post value result)


val montgomery_multiply_sfe_by_fer #b1 #b2 (fe:i32_b b1) (fer: i32_b b2)
    : Pure (i32_b (nat_div_ceil (b1 * b2) (v v_MONTGOMERY_R) + 1665))
      (requires (b1 * b2 < pow2_31))
      (ensures (fun result -> 
          montgomery_post (mul_i32_b fe fer) (result)))
      

val to_standard_domain #b (mfe: i32_b b) 
    : Pure (i32_b (nat_div_ceil (b * 1353) (v v_MONTGOMERY_R) + 1665))
      (requires (b * 1353 < pow2_31))
      (ensures (fun result -> 
          montgomery_post (mul_i32_b mfe (1353l <: i32_b 1353)) result))


val to_unsigned_representative (fe: wfFieldElement)
    : Prims.Pure (int_t_d u16_inttype 12)
      (requires True)
      (ensures
        fun result ->
          let result:u16 = result in
          v result == to_spec_fe fe /\
          result >=. 0us &&
          result <. (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u16))

type t_PolynomialRingElement = { f_coefficients:t_Array (t_FieldElement) (sz 256) }

type t_PolynomialRingElement_b b = { f_coefficients:t_Array (i32_b b) (sz 256) }

type wfPolynomialRingElement = t_PolynomialRingElement_b (v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS - 1)

val derefine_poly_b (#b1:nat) (x:t_PolynomialRingElement_b b1):  
    r:t_PolynomialRingElement{
    forall (i:usize). v i < 256 ==> (r.f_coefficients.[i] <: i32) ==  (x.f_coefficients.[i] <: i32)}

val derefine_vector_b (#v_K:usize) (#b:nat) (x:t_Array (t_PolynomialRingElement_b b) v_K):
    r:t_Array t_PolynomialRingElement v_K{
    forall (i:usize). (v i < v v_K) ==>
     (let ri : t_PolynomialRingElement = r.[i] in
      let xi : t_PolynomialRingElement_b b = x.[i] in
      ri == derefine_poly_b xi)}

val derefine_matrix_b (#v_K:usize) (#b:nat) 
  (x:t_Array (t_Array (t_PolynomialRingElement_b b) v_K) v_K) :
    r:t_Array (t_Array t_PolynomialRingElement v_K) v_K{
    forall (i:usize). (v i < v v_K) ==>
     (let ri : t_Array (t_PolynomialRingElement) v_K = r.[i] in
      let xi : t_Array (t_PolynomialRingElement_b b) v_K = x.[i] in
      ri == derefine_vector_b xi)}


val cast_poly_b (#b1:nat) (#b2:nat{b1 <= b2 /\ b2 < pow2_31}) 
  (x:t_PolynomialRingElement_b b1)
  : Pure (t_PolynomialRingElement_b b2) 
    (requires True)
    (ensures fun r -> derefine_poly_b x == derefine_poly_b r)

val cast_vector_b (#v_K:usize) (#b1:nat) (#b2:nat{b1 <= b2 /\ b2 < pow2_31}) 
  (x:t_Array (t_PolynomialRingElement_b b1) v_K)
  : Pure (t_Array (t_PolynomialRingElement_b b2) v_K)
    (requires True)
    (ensures fun r -> derefine_vector_b x == derefine_vector_b r)

let poly_range (#b:nat) (x:t_PolynomialRingElement_b b) (b':nat) =
  (forall (i:usize). v i < 256 ==> i32_range (x.f_coefficients.[i] <: i32) b')

let vector_range (#v_K:usize) (#b:nat) (x:t_Array (t_PolynomialRingElement_b b) v_K) (b':nat) =
  (forall (i:usize). v i < v v_K ==> poly_range #b x.[i] b')

val down_cast_poly_b (#b1:nat) (#b2:nat{b2 <= b1 /\ b1 < pow2_31}) 
  (x:t_PolynomialRingElement_b b1): 
  Pure (t_PolynomialRingElement_b b2)
  (requires (poly_range x b2))
  (ensures fun r ->  derefine_poly_b x == derefine_poly_b r) 

val down_cast_vector_b (#v_K:usize) (#b1:nat) (#b2:nat{b2 <= b1 /\ b1 < pow2_31}) 
  (x:t_Array (t_PolynomialRingElement_b b1) v_K): 
  Pure (t_Array (t_PolynomialRingElement_b b2) v_K)
  (requires (vector_range x b2))
  (ensures fun r ->  derefine_vector_b x == derefine_vector_b r) 

let op_String_Access #t #l (a:t_Array t l) (i:usize{v i < v l}) : t = a.[i]

let wf_poly_to_spec_poly (re: wfPolynomialRingElement): Spec.Kyber.polynomial =
    let p = Spec.Kyber.map' (fun x -> wf_fe_to_spec_fe x <: nat) re.f_coefficients in
    introduce forall i. Seq.index p i < v Spec.Kyber.v_FIELD_MODULUS
    with assert (Seq.index p i == Seq.index p (v (sz i)));
    p

let to_spec_poly (m:t_PolynomialRingElement) : (Spec.Kyber.polynomial) =
    let p = createi #nat (sz 256) (fun i -> to_spec_fe (m.f_coefficients.[i])) in
    assert (forall i. Seq.index p i = to_spec_fe (m.f_coefficients.[sz i]));
    assert (forall i. Seq.index p i < v Spec.Kyber.v_FIELD_MODULUS);
    p

let to_spec_poly_b #b (m:t_PolynomialRingElement_b b) : (Spec.Kyber.polynomial) =
    to_spec_poly (derefine_poly_b m)

let mont_to_spec_poly (m:t_PolynomialRingElement) : (Spec.Kyber.polynomial) =
    let p = createi #nat (sz 256) (fun i -> mont_to_spec_fe (m.f_coefficients.[i])) in
    assert (forall i. Seq.index p i = mont_to_spec_fe (m.f_coefficients.[sz i]));
    assert (forall i. Seq.index p i < v Spec.Kyber.v_FIELD_MODULUS);
    p


let to_spec_vector (#p:Spec.Kyber.params)
                   (m:t_Array (t_PolynomialRingElement) p.v_RANK)
                   : (Spec.Kyber.vector p) =
    createi p.v_RANK (fun i -> to_spec_poly (m.[i]))


let to_spec_vector_b (#p:Spec.Kyber.params) (#b:nat)
                   (m:t_Array (t_PolynomialRingElement_b b) p.v_RANK)
                   : (Spec.Kyber.vector p) =
    to_spec_vector (derefine_vector_b m)

let mont_to_spec_vector (#p:Spec.Kyber.params)
                   (m:t_Array (t_PolynomialRingElement) p.v_RANK)
                   : (Spec.Kyber.vector p) =
    createi p.v_RANK (fun i -> mont_to_spec_poly (m.[i]))

let mont_to_spec_vector_b (#p:Spec.Kyber.params) (#b:nat)
                   (m:t_Array (t_PolynomialRingElement_b b) p.v_RANK)
                   : (Spec.Kyber.vector p) =
    mont_to_spec_vector (derefine_vector_b m)

let to_spec_matrix (#p:Spec.Kyber.params) 
                   (m:(t_Array (t_Array (t_PolynomialRingElement) p.v_RANK) p.v_RANK))
                   : (Spec.Kyber.matrix p) =
    createi p.v_RANK (fun i -> to_spec_vector (m.[i]))

let to_spec_matrix_b (#p:Spec.Kyber.params) (#b:nat)
                   (m:(t_Array (t_Array (t_PolynomialRingElement_b b) p.v_RANK) p.v_RANK))
                   : (Spec.Kyber.matrix p) =
    to_spec_matrix (derefine_matrix_b m)

let mont_to_spec_matrix (#p:Spec.Kyber.params) 
                   (m:(t_Array (t_Array (t_PolynomialRingElement) p.v_RANK) p.v_RANK))
                   : (Spec.Kyber.matrix p) =
    createi p.v_RANK (fun i -> mont_to_spec_vector (m.[i]))

let impl__PolynomialRingElement__ZERO: t_PolynomialRingElement_b 1 =
  { f_coefficients = Rust_primitives.Hax.repeat (0l <: i32_b 1) (sz 256) } <: t_PolynomialRingElement_b 1

val add_to_ring_element (#b1:nat) (#b2:nat{b1 + b2 < pow2_31}) (v_K: usize) (lhs: t_PolynomialRingElement_b b1) (rhs: t_PolynomialRingElement_b b2)
    : Prims.Pure (t_PolynomialRingElement_b (b1 + b2))
      (requires True) 
      (ensures fun result ->
        (forall i. v result.f_coefficients.[i] == v lhs.f_coefficients.[i] + v rhs.f_coefficients.[i]))




