module Libcrux.Kem.Kyber.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_FieldElement = i32

unfold
let t_FieldElementTimesMontgomeryR = i32

unfold
let t_MontgomeryFieldElement = i32

let v_BARRETT_MULTIPLIER: i64 = 20159L

let v_BARRETT_SHIFT: i64 = 26L

let v_BARRETT_R: i64 = 1L <<! v_BARRETT_SHIFT

let v_INVERSE_OF_MODULUS_MOD_R: u32 = 62209ul

let v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i32 = 1353l

let v_MONTGOMERY_SHIFT: u8 = 16uy

val v_MONTGOMERY_R: x:i32{v x = pow2 16}

let to_spec_fe (m:t_FieldElement) : Spec.Kyber.field_element = 
    let m_v = v m % v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS in
    assert (m_v > -  v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS);
    if m_v < 0 then
      m_v + v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
    else m_v

val mont_to_spec_fe (m:t_FieldElement)
    : Spec.Kyber.field_element

val get_n_least_significant_bits (n: u8 {v n > 0 /\ v n <= 32}) (value: u32)
    : Prims.Pure (int_t_d u32_inttype (v n))
      (requires v n < 32)
      (ensures
        fun result ->
          let result:u32 = result in
          v result = v value % pow2 (v n))


let barrett_pre (value:i32) = 
    v value <= v v_BARRETT_R /\ v value >= - v v_BARRETT_R
// Appears to work up to +/- 2^28, but not at +/- 2^29

let barrett_post (value:i32) (result:i32) = 
    v result % v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS =
    v value % v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS /\
    v result > - (v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS) /\
    v result < (v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS)

val barrett_reduce (value: i32)
    : Prims.Pure i32
    (requires barrett_pre value)
    (ensures barrett_post value)

let montgomery_post (value:i32) (result:i32) =
    v result % v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS =
    (v value / v v_MONTGOMERY_R) % v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS /\
   (let abs_v = abs (v value) in
    v result >= - (abs_v / v v_MONTGOMERY_R) - v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS / 2 /\
    v result <= (abs_v / v v_MONTGOMERY_R) + v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS / 2)

val montgomery_reduce (value: i32)
    : Prims.Pure i32
      (requires True)
      (ensures
        fun result ->
          let result:i32 = result in
          montgomery_post value result)


val montgomery_multiply_sfe_by_fer (fe fer: i32) 
    : Pure i32
      (requires (range (v fe * v fer) i32_inttype))
      (ensures (fun result -> 
          montgomery_post (fe *! fer) (result)))
      

val to_standard_domain (mfe: i32) 
    : Pure i32
      (requires (range (v mfe * 1353) i32_inttype))
      (ensures (fun result -> 
          montgomery_post (mfe *! 1353l) result))

let to_unsigned_representative_pre (fe: i32)
  = fe >=. (Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) &&
    fe <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS

val to_unsigned_representative (fe: i32)
    : Prims.Pure (int_t_d u16_inttype 12)
      (requires to_unsigned_representative_pre fe)
      (ensures
        fun result ->
          let result:u16 = result in
          result >=. 0us &&
          result <. (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u16))

type t_PolynomialRingElement = { f_coefficients:t_Array i32 (sz 256) }

let op_String_Access #t #l (a:t_Array t l) (i:usize{v i < v l}) : t = a.[i]

let to_spec_poly (m:t_PolynomialRingElement) : (Spec.Kyber.polynomial) =
    let p = createi #nat (sz 256) (fun i -> to_spec_fe (m.f_coefficients.[i])) in
    assert (forall i. Seq.index p i = to_spec_fe (m.f_coefficients.[sz i]));
    assert (forall i. Seq.index p i < v Spec.Kyber.v_FIELD_MODULUS);
    p

let mont_to_spec_poly (m:t_PolynomialRingElement) : (Spec.Kyber.polynomial) =
    let p = createi #nat (sz 256) (fun i -> mont_to_spec_fe (m.f_coefficients.[i])) in
    assert (forall i. Seq.index p i = mont_to_spec_fe (m.f_coefficients.[sz i]));
    assert (forall i. Seq.index p i < v Spec.Kyber.v_FIELD_MODULUS);
    p

let to_spec_vector (#p:Spec.Kyber.params)
                   (m:t_Array t_PolynomialRingElement p.v_RANK)
                   : (Spec.Kyber.vector p) =
    createi p.v_RANK (fun i -> to_spec_poly (m.[i]))

let mont_to_spec_vector (#p:Spec.Kyber.params)
                   (m:t_Array t_PolynomialRingElement p.v_RANK)
                   : (Spec.Kyber.vector p) =
    createi p.v_RANK (fun i -> mont_to_spec_poly (m.[i]))

let to_spec_matrix (#p:Spec.Kyber.params)
                   (m:(t_Array (t_Array t_PolynomialRingElement p.v_RANK) p.v_RANK))
                   : (Spec.Kyber.matrix p) =
    createi p.v_RANK (fun i -> to_spec_vector (m.[i]))

let mont_to_spec_matrix (#p:Spec.Kyber.params)
                   (m:(t_Array (t_Array t_PolynomialRingElement p.v_RANK) p.v_RANK))
                   : (Spec.Kyber.matrix p) =
    createi p.v_RANK (fun i -> mont_to_spec_vector (m.[i]))

let impl__PolynomialRingElement__ZERO: t_PolynomialRingElement =
  { f_coefficients = Rust_primitives.Hax.repeat 0l (sz 256) } <: t_PolynomialRingElement

val add_to_ring_element (v_K: usize) (lhs rhs: t_PolynomialRingElement)
    : Prims.Pure t_PolynomialRingElement
      (requires forall i. range (v lhs.f_coefficients.[i] + v rhs.f_coefficients.[i]) i32_inttype)
      (ensures fun result ->
        (forall i. v result.f_coefficients.[i] == v lhs.f_coefficients.[i] + v rhs.f_coefficients.[i]))




