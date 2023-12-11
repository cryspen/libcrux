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

val v_BARRETT_R: x:i64{v x = pow2 26}

let v_INVERSE_OF_MODULUS_MOD_R: u32 = 62209ul

let v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i32 = 1353l

let v_MONTGOMERY_SHIFT: u8 = 16uy

val v_MONTGOMERY_R: x:i32{v x = pow2 16}

type t_PolynomialRingElement = { f_coefficients:t_Array i32 (sz 256) }

let op_String_Access #t #l (a:t_Array t l) (i:usize{v i < v l}) : t = a.[i]

val createi #t (l:usize) (f:(u:usize{u <. l} -> t))
    : Pure (t_Array t l)
      (requires True)
      (ensures (fun res -> (forall i. res.[i] == f i)))

let to_spec_fe (m:t_FieldElement) : Spec.Kyber.field_element = 
    let m_v = v m % v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS in
    assert (m_v > -  v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS);
    if m_v < 0 then
      m_v + v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
    else m_v

val mont_to_spec_fe (m:t_FieldElement)
    : Spec.Kyber.field_element


let to_spec_poly (m:t_PolynomialRingElement) : (Spec.Kyber.polynomial) =
    createi (sz 256) (fun i -> to_spec_fe (m.f_coefficients.[i]))

let mont_to_spec_poly (m:t_PolynomialRingElement) : (Spec.Kyber.polynomial) =
    createi (sz 256) (fun i -> mont_to_spec_fe (m.f_coefficients.[i]))

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


val get_n_least_significant_bits (n: u8) (value: u32)
    : Prims.Pure u32
      (requires n =. 4uy || n =. 5uy || n =. 10uy || n =. 11uy || n =. v_MONTGOMERY_SHIFT)
      (ensures
        fun result ->
          let result:u32 = result in
          v result = v value % pow2 (v n))


let barrett_pre (value:int) = 
    value > - (pow2 26) /\
    value < pow2 26

val barrett_reduce (value: i32)
    : Prims.Pure i32
      (requires (barrett_pre (v value)))
      (ensures
        fun result ->
          let result:i32 = result in
          v result = to_spec_fe value)
//          result >. (Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) &&
//          result <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS)


let montgomery_pre (value:int) =
        value >=
        (v (neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS) * v v_MONTGOMERY_R) /\
        value <= (v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS * v v_MONTGOMERY_R)

let montgomery_post_range (output:i32) =
          output >=.
          (neg (3l *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) /! 2l) /\
          output <=. (3l *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) /! 2l

val montgomery_reduce (value: i32)
    : Prims.Pure i32
      (requires (montgomery_pre (v value)))
      (ensures
        fun result ->
          let result:i32 = result in
          montgomery_post_range result)


val montgomery_multiply_sfe_by_fer (fe fer: i32) 
    : Pure i32
      (requires (montgomery_pre (v fe * v fer)))
      (ensures (fun result -> 
          montgomery_post_range result))
      

val to_standard_domain (mfe: i32) 
    : Pure i32
      (requires (montgomery_pre (v mfe * v v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS)))
      (ensures (fun result -> 
          montgomery_post_range result))

val to_unsigned_representative (fe: i32)
    : Prims.Pure u16
      (requires
        fe >=. (Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) &&
        fe <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS)
      (ensures
        fun result ->
          let result:u16 = result in
          result >=. 0us &&
          result <. (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u16))

let impl__PolynomialRingElement__ZERO: t_PolynomialRingElement =
  { f_coefficients = Rust_primitives.Hax.repeat 0l (sz 256) } <: t_PolynomialRingElement

val add_to_ring_element (v_K: usize) (lhs rhs: t_PolynomialRingElement)
    : Prims.Pure t_PolynomialRingElement
      (requires
        v_K >. sz 1 /\
        v_K <=. sz 4 /\
        (forall i. v lhs.f_coefficients.[i] >= -(v v_K - 1) * v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS) /\
        (forall i. v lhs.f_coefficients.[i] <= (v v_K - 1) * v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS) /\
        (forall i. v rhs.f_coefficients.[i] >= -v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS) /\
        (forall i. v rhs.f_coefficients.[i] <= v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS)
       )
      (ensures fun result ->
        (forall i. v result.f_coefficients.[i] >= -v v_K * v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS) /\
        (forall i. v result.f_coefficients.[i] <= v v_K * v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS))
