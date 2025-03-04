//! A module for serializing and deserializing PortableVector
//! Verification status: Lax

// A general style adopted here is to first define an internal function
// called serialize_N_int or deserialize_N_int that (de)serializes
// the minimal number of inputs K such that N*K is a multiple of 8.
// These functions are then called multiple times in the main function,
// called serialize_N or deserialize_N.
// This refactoring reduces redundancy, and also makes the code easier for
// F* to handle. As a general rule, any function that modifies an array
// more than 8 times with complex expressions starts to strain F*, so
// we separate out the code that does the computation (in _int functions)
// and code that updates arrays (in the outer functions).

use super::vector_type::*;

#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--compat_pre_core 2 --z3rlimit 300 --z3refresh\"

let serialize_1_bit_vec_lemma (v: t_Array i16 (sz 16))
  (_: squash (forall i. Rust_primitives.bounded (Seq.index v i) 1))
   : squash (
     let inputs = bit_vec_of_int_t_array v 1 in
     let outputs = bit_vec_of_int_t_array (${serialize_1} ({ f_elements = v })) 8 in
     (forall (i: nat {i < 16}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options
"
    )
)]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--z3rlimit 300\"

let serialize_1_lemma inputs =
  serialize_1_bit_vec_lemma inputs.f_elements ();
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (${serialize_1} inputs) 8) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs.f_elements 1))

#pop-options
"
    )
)]
#[cfg_attr(hax, hax_lib::fstar::after(interface, "
val serialize_1_lemma (inputs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) : Lemma
  (requires (forall i. Rust_primitives.bounded (Seq.index inputs.f_elements i) 1)) 
  (ensures bit_vec_of_int_t_array (${serialize_1} inputs) 8 == bit_vec_of_int_t_array inputs.f_elements 1)
"))]
#[inline(always)]
pub(crate) fn serialize_1(v: PortableVector, out: &mut [u8]) {
    debug_assert!(out.len() == 2);
    
    out[0] = (v.elements[0] as u8)
        | ((v.elements[1] as u8) << 1)
        | ((v.elements[2] as u8) << 2)
        | ((v.elements[3] as u8) << 3)
        | ((v.elements[4] as u8) << 4)
        | ((v.elements[5] as u8) << 5)
        | ((v.elements[6] as u8) << 6)
        | ((v.elements[7] as u8) << 7);
    out[1] = (v.elements[8] as u8)
        | ((v.elements[9] as u8) << 1)
        | ((v.elements[10] as u8) << 2)
        | ((v.elements[11] as u8) << 3)
        | ((v.elements[12] as u8) << 4)
        | ((v.elements[13] as u8) << 5)
        | ((v.elements[14] as u8) << 6)
        | ((v.elements[15] as u8) << 7);
}

//deserialize_1_bit_vec_lemma
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--compat_pre_core 2 --z3rlimit 300 --z3refresh\"

let deserialize_1_bit_vec_lemma (v: t_Array u8 (sz 2))
   : squash (
     let inputs = bit_vec_of_int_t_array v 8 in
     let outputs = bit_vec_of_int_t_array (${deserialize_1} v).f_elements 1 in
     (forall (i: nat {i < 16}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options
"
    )
)]
//deserialize_1_lemma
#[cfg_attr(hax, hax_lib::fstar::after(interface, "
val deserialize_1_lemma (inputs: t_Array u8 (sz 2)) : Lemma
  (ensures bit_vec_of_int_t_array (${deserialize_1} inputs).f_elements 1 == bit_vec_of_int_t_array inputs 8)
"))]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--z3rlimit 300\"

let deserialize_1_lemma inputs =
  deserialize_1_bit_vec_lemma inputs;
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (${deserialize_1} inputs).f_elements 1) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs 8))

#pop-options
"
    )
)]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
let deserialize_1_bounded_lemma inputs =
  admit()
"
    )
)]
//deserialize_1_bounded_lemma
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        interface,
        "
val deserialize_1_bounded_lemma (inputs: t_Array u8 (sz 2)) : Lemma
  (ensures forall i. i < 16 ==> bounded (Seq.index (${deserialize_1} inputs).f_elements i) 1)
"
    )
)]
#[hax_lib::requires(fstar!(r#"
     ${v.len() == 2}
"#))]
#[inline(always)]
pub(crate) fn deserialize_1(v: &[u8], out: &mut PortableVector) {
    out.elements[0] = (v[0] & 0x1) as i16;
    out.elements[1] = ((v[0] >> 1) & 0x1) as i16;
    out.elements[2] = ((v[0] >> 2) & 0x1) as i16;
    out.elements[3] = ((v[0] >> 3) & 0x1) as i16;
    out.elements[4] = ((v[0] >> 4) & 0x1) as i16;
    out.elements[5] = ((v[0] >> 5) & 0x1) as i16;
    out.elements[6] = ((v[0] >> 6) & 0x1) as i16;
    out.elements[7] = ((v[0] >> 7) & 0x1) as i16;
    out.elements[8] = (v[1] & 0x1) as i16;
    out.elements[9] = ((v[1] >> 1) & 0x1) as i16;
    out.elements[10] = ((v[1] >> 2) & 0x1) as i16;
    out.elements[11] = ((v[1] >> 3) & 0x1) as i16;
    out.elements[12] = ((v[1] >> 4) & 0x1) as i16;
    out.elements[13] = ((v[1] >> 5) & 0x1) as i16;
    out.elements[14] = ((v[1] >> 6) & 0x1) as i16;
    out.elements[15] = ((v[1] >> 7) & 0x1) as i16;
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
     ${v.len() == 8}
"#))]
pub(crate) fn serialize_4_int(v: &[i16]) -> (u8, u8, u8, u8) {
    let result0 = ((v[1] as u8) << 4) | (v[0] as u8);
    let result1 = ((v[3] as u8) << 4) | (v[2] as u8);
    let result2 = ((v[5] as u8) << 4) | (v[4] as u8);
    let result3 = ((v[7] as u8) << 4) | (v[6] as u8);
    (result0, result1, result2, result3)
}

#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--compat_pre_core 2 --z3rlimit 300 --z3refresh\"

let serialize_4_bit_vec_lemma (v: t_Array i16 (sz 16))
  (_: squash (forall i. Rust_primitives.bounded (Seq.index v i) 4))
   : squash (
     let inputs = bit_vec_of_int_t_array v 4 in
     let outputs = bit_vec_of_int_t_array (${serialize_4} ({ f_elements = v })) 8 in
     (forall (i: nat {i < 64}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options
"
    )
)]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--z3rlimit 300\"

let serialize_4_lemma inputs =
  serialize_4_bit_vec_lemma inputs.f_elements ();
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (${serialize_4} inputs) 8) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs.f_elements 4))

#pop-options
"
    )
)]
#[cfg_attr(hax, hax_lib::fstar::after(interface, "
val serialize_4_lemma (inputs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) : Lemma
  (requires (forall i. Rust_primitives.bounded (Seq.index inputs.f_elements i) 4)) 
  (ensures bit_vec_of_int_t_array (${serialize_4} inputs) 8 == bit_vec_of_int_t_array inputs.f_elements 4)
"))]
#[inline(always)]
pub(crate) fn serialize_4(v: PortableVector, out: &mut [u8]) {
    debug_assert!(out.len() == 8);
    (out[0], out[1], out[2], out[3]) = serialize_4_int(&v.elements[0..8]);
    (out[4], out[5], out[6], out[7]) = serialize_4_int(&v.elements[8..16]);
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
     ${bytes.len() == 4}
"#))]
pub(crate) fn deserialize_4_int(bytes: &[u8]) -> (i16, i16, i16, i16, i16, i16, i16, i16) {
    let v0 = (bytes[0] & 0x0F) as i16;
    let v1 = ((bytes[0] >> 4) & 0x0F) as i16;
    let v2 = (bytes[1] & 0x0F) as i16;
    let v3 = ((bytes[1] >> 4) & 0x0F) as i16;
    let v4 = (bytes[2] & 0x0F) as i16;
    let v5 = ((bytes[2] >> 4) & 0x0F) as i16;
    let v6 = (bytes[3] & 0x0F) as i16;
    let v7 = ((bytes[3] >> 4) & 0x0F) as i16;
    (v0, v1, v2, v3, v4, v5, v6, v7)
}

//deserialize_4_bounded_lemma
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        interface,
        "
val deserialize_4_bounded_lemma (inputs: t_Array u8 (sz 8)) : Lemma
  (ensures forall i. i < 16 ==> bounded (Seq.index (${deserialize_4} inputs).f_elements i) 4)
"
    )
)]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
let deserialize_4_bounded_lemma inputs =
  admit()
"
    )
)]
//deserialize_4_bit_vec_lemma
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--compat_pre_core 2 --z3rlimit 300 --z3refresh\"

let deserialize_4_bit_vec_lemma (v: t_Array u8 (sz 8))
   : squash (
     let inputs = bit_vec_of_int_t_array v 8 in
     let outputs = bit_vec_of_int_t_array (${deserialize_4} v).f_elements 4 in
     (forall (i: nat {i < 64}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options
"
    )
)]
//deserialize_4_lemma
#[cfg_attr(hax, hax_lib::fstar::after(interface, "
val deserialize_4_lemma (inputs: t_Array u8 (sz 8)) : Lemma
  (ensures bit_vec_of_int_t_array (${deserialize_4} inputs).f_elements 4 == bit_vec_of_int_t_array inputs 8)
"))]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--z3rlimit 300\"

let deserialize_4_lemma inputs =
  deserialize_4_bit_vec_lemma inputs;
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (${deserialize_4} inputs).f_elements 4) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs 8))

#pop-options
"
    )
)]
#[hax_lib::requires(fstar!(r#"
     ${bytes.len() == 8}
"#))]
#[inline(always)]
pub(crate) fn deserialize_4(bytes: &[u8], out: &mut PortableVector) {
    (
        out.elements[0],
        out.elements[1],
        out.elements[2],
        out.elements[3],
        out.elements[4],
        out.elements[5],
        out.elements[6],
        out.elements[7],
    ) = deserialize_4_int(&bytes[0..4]);
    (
        out.elements[8],
        out.elements[9],
        out.elements[10],
        out.elements[11],
        out.elements[12],
        out.elements[13],
        out.elements[14],
        out.elements[15],
    ) = deserialize_4_int(&bytes[4..8]);
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
     ${v.len() == 8}
"#))]
pub(crate) fn serialize_5_int(v: &[i16]) -> (u8, u8, u8, u8, u8) {
    let r0 = (v[0] | v[1] << 5) as u8;
    let r1 = (v[1] >> 3 | v[2] << 2 | v[3] << 7) as u8;
    let r2 = (v[3] >> 1 | v[4] << 4) as u8;
    let r3 = (v[4] >> 4 | v[5] << 1 | v[6] << 6) as u8;
    let r4 = (v[6] >> 2 | v[7] << 3) as u8;
    (r0, r1, r2, r3, r4)
}

#[inline(always)]
pub(crate) fn serialize_5(v: PortableVector, out: &mut [u8]) {
    debug_assert!(out.len() == 10);
    (out[0], out[1], out[2], out[3], out[4]) = serialize_5_int(&v.elements[0..8]);
    (out[5], out[6], out[7], out[8], out[9]) = serialize_5_int(&v.elements[8..16]);
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
     ${bytes.len() == 5}
"#))]
pub(crate) fn deserialize_5_int(bytes: &[u8]) -> (i16, i16, i16, i16, i16, i16, i16, i16) {
    let v0 = (bytes[0] & 0x1F) as i16;
    let v1 = ((bytes[1] & 0x3) << 3 | (bytes[0] >> 5)) as i16;
    let v2 = ((bytes[1] >> 2) & 0x1F) as i16;
    let v3 = (((bytes[2] & 0xF) << 1) | (bytes[1] >> 7)) as i16;
    let v4 = (((bytes[3] & 1) << 4) | (bytes[2] >> 4)) as i16;
    let v5 = ((bytes[3] >> 1) & 0x1F) as i16;
    let v6 = (((bytes[4] & 0x7) << 2) | (bytes[3] >> 6)) as i16;
    let v7 = (bytes[4] >> 3) as i16;
    (v0, v1, v2, v3, v4, v5, v6, v7)
}

#[hax_lib::requires(fstar!(r#"
     ${bytes.len() == 10}
"#))]
#[inline(always)]
pub(crate) fn deserialize_5(bytes: &[u8], out: &mut PortableVector) {
    (
        out.elements[0],
        out.elements[1],
        out.elements[2],
        out.elements[3],
        out.elements[4],
        out.elements[5],
        out.elements[6],
        out.elements[7],
    ) = deserialize_5_int(&bytes[0..5]);
    (
        out.elements[8],
        out.elements[9],
        out.elements[10],
        out.elements[11],
        out.elements[12],
        out.elements[13],
        out.elements[14],
        out.elements[15],
    ) = deserialize_5_int(&bytes[5..10]);
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
     ${v.len() == 4}
"#))]
pub(crate) fn serialize_10_int(v: &[i16]) -> (u8, u8, u8, u8, u8) {
    let r0 = (v[0] & 0xFF) as u8;
    let r1 = ((v[1] & 0x3F) as u8) << 2 | ((v[0] >> 8) & 0x03) as u8;
    let r2 = ((v[2] & 0x0F) as u8) << 4 | ((v[1] >> 6) & 0x0F) as u8;
    let r3 = ((v[3] & 0x03) as u8) << 6 | ((v[2] >> 4) & 0x3F) as u8;
    let r4 = ((v[3] >> 2) & 0xFF) as u8;
    (r0, r1, r2, r3, r4)
}

#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--compat_pre_core 2 --z3rlimit 300 --z3refresh\"

let serialize_10_bit_vec_lemma (v: t_Array i16 (sz 16))
  (_: squash (forall i. Rust_primitives.bounded (Seq.index v i) 10))
   : squash (
     let inputs = bit_vec_of_int_t_array v 10 in
     let outputs = bit_vec_of_int_t_array (${serialize_10} ({ f_elements = v })) 8 in
     (forall (i: nat {i < 160}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options
"
    )
)]
#[cfg_attr(hax, hax_lib::fstar::after(interface, "
val serialize_10_lemma (inputs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) : Lemma
  (requires (forall i. Rust_primitives.bounded (Seq.index inputs.f_elements i) 10)) 
  (ensures bit_vec_of_int_t_array (${serialize_10} inputs) 8 == bit_vec_of_int_t_array inputs.f_elements 10)
"))]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--z3rlimit 300\"

let serialize_10_lemma inputs =
  serialize_10_bit_vec_lemma inputs.f_elements ();
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (${serialize_10} inputs) 8) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs.f_elements 10))

#pop-options
"
    )
)]
#[inline(always)]
pub(crate) fn serialize_10(v: PortableVector, out: &mut [u8]) {
    debug_assert!(out.len() == 20);
    (out[0], out[1], out[2], out[3], out[4]) = serialize_10_int(&v.elements[0..4]);
    (out[5], out[6], out[7], out[8], out[9]) = serialize_10_int(&v.elements[4..8]);
    (out[10], out[11], out[12], out[13], out[14]) = serialize_10_int(&v.elements[8..12]);
    (out[15], out[16], out[17], out[18], out[19]) = serialize_10_int(&v.elements[12..16]);
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
     ${bytes.len() == 10}
"#))]
pub(crate) fn deserialize_10_int(bytes: &[u8]) -> (i16, i16, i16, i16, i16, i16, i16, i16) {
    let r0 = ((bytes[1] as i16 & 0x03) << 8 | (bytes[0] as i16 & 0xFF)) as i16;
    let r1 = ((bytes[2] as i16 & 0x0F) << 6 | (bytes[1] as i16 >> 2)) as i16;
    let r2 = ((bytes[3] as i16 & 0x3F) << 4 | (bytes[2] as i16 >> 4)) as i16;
    let r3 = (((bytes[4] as i16) << 2) | (bytes[3] as i16 >> 6)) as i16;
    let r4 = ((bytes[6] as i16 & 0x03) << 8 | (bytes[5] as i16 & 0xFF)) as i16;
    let r5 = ((bytes[7] as i16 & 0x0F) << 6 | (bytes[6] as i16 >> 2)) as i16;
    let r6 = ((bytes[8] as i16 & 0x3F) << 4 | (bytes[7] as i16 >> 4)) as i16;
    let r7 = (((bytes[9] as i16) << 2) | (bytes[8] as i16 >> 6)) as i16;
    (r0, r1, r2, r3, r4, r5, r6, r7)
}

//deserialize_10_bit_vec_lemma
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--compat_pre_core 2 --z3rlimit 300 --z3refresh\"

let deserialize_10_bit_vec_lemma (v: t_Array u8 (sz 20))
   : squash (
     let inputs = bit_vec_of_int_t_array v 8 in
     let outputs = bit_vec_of_int_t_array (${deserialize_10} v).f_elements 10 in
     (forall (i: nat {i < 160}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options
"
    )
)]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--z3rlimit 300\"

let deserialize_10_lemma inputs =
  deserialize_10_bit_vec_lemma inputs;
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (${deserialize_10} inputs).f_elements 10) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs 8))

#pop-options
"
    )
)]
//deserialize_10_lemma
#[cfg_attr(hax, hax_lib::fstar::after(interface, "
val deserialize_10_lemma (inputs: t_Array u8 (sz 20)) : Lemma
  (ensures bit_vec_of_int_t_array (${deserialize_10} inputs).f_elements 10 == bit_vec_of_int_t_array inputs 8)
"))]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
let deserialize_10_bounded_lemma inputs =
  admit()
"
    )
)]
//deserialize_10_bounded_lemma
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        interface,
        "
val deserialize_10_bounded_lemma (inputs: t_Array u8 (sz 20)) : Lemma
  (ensures forall i. i < 16 ==> bounded (Seq.index (${deserialize_10} inputs).f_elements i) 10)
"
    )
)]
#[hax_lib::requires(fstar!(r#"
     ${bytes.len() == 20}
"#))]
#[inline(always)]
pub(crate) fn deserialize_10(bytes: &[u8], out: &mut PortableVector) {
    (
        out.elements[0],
        out.elements[1],
        out.elements[2],
        out.elements[3],
        out.elements[4],
        out.elements[5],
        out.elements[6],
        out.elements[7],
    ) = deserialize_10_int(&bytes[0..10]);
    (
        out.elements[8],
        out.elements[9],
        out.elements[10],
        out.elements[11],
        out.elements[12],
        out.elements[13],
        out.elements[14],
        out.elements[15],
    ) = deserialize_10_int(&bytes[10..20]);
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
     ${v.len() == 8}
"#))]
pub(crate) fn serialize_11_int(v: &[i16]) -> (u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8) {
    let r0 = v[0] as u8;
    let r1 = ((v[1] & 0x1F) as u8) << 3 | ((v[0] >> 8) as u8);
    let r2 = ((v[2] & 0x3) as u8) << 6 | ((v[1] >> 5) as u8);
    let r3 = ((v[2] >> 2) & 0xFF) as u8;
    let r4 = ((v[3] & 0x7F) as u8) << 1 | (v[2] >> 10) as u8;
    let r5 = ((v[4] & 0xF) as u8) << 4 | (v[3] >> 7) as u8;
    let r6 = ((v[5] & 0x1) as u8) << 7 | (v[4] >> 4) as u8;
    let r7 = ((v[5] >> 1) & 0xFF) as u8;
    let r8 = ((v[6] & 0x3F) as u8) << 2 | (v[5] >> 9) as u8;
    let r9 = ((v[7] & 0x7) as u8) << 5 | (v[6] >> 6) as u8;
    let r10 = (v[7] >> 3) as u8;
    (r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10)
}

#[inline(always)]
pub(crate) fn serialize_11(v: PortableVector, out: &mut [u8]) {
    debug_assert!(out.len() == 22);
    (
        out[0], out[1], out[2], out[3], out[4], out[5], out[6], out[7], out[8], out[9], out[10],
    ) = serialize_11_int(&v.elements[0..8]);
    (
        out[11], out[12], out[13], out[14], out[15], out[16], out[17], out[18], out[19], out[20],
        out[21],
    ) = serialize_11_int(&v.elements[8..16]);
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
     ${bytes.len() == 11}
"#))]
pub(crate) fn deserialize_11_int(bytes: &[u8]) -> (i16, i16, i16, i16, i16, i16, i16, i16) {
    let r0 = (bytes[1] as i16 & 0x7) << 8 | bytes[0] as i16;
    let r1 = (bytes[2] as i16 & 0x3F) << 5 | (bytes[1] as i16 >> 3);
    let r2 = (bytes[4] as i16 & 0x1) << 10 | ((bytes[3] as i16) << 2) | ((bytes[2] as i16) >> 6);
    let r3 = (bytes[5] as i16 & 0xF) << 7 | (bytes[4] as i16 >> 1);
    let r4 = (bytes[6] as i16 & 0x7F) << 4 | (bytes[5] as i16 >> 4);
    let r5 = (bytes[8] as i16 & 0x3) << 9 | ((bytes[7] as i16) << 1) | ((bytes[6] as i16) >> 7);
    let r6 = (bytes[9] as i16 & 0x1F) << 6 | (bytes[8] as i16 >> 2);
    let r7 = ((bytes[10] as i16) << 3) | (bytes[9] as i16 >> 5);
    (r0, r1, r2, r3, r4, r5, r6, r7)
}

#[hax_lib::requires(fstar!(r#"
     ${bytes.len() == 22}
"#))]
#[inline(always)]
pub(crate) fn deserialize_11(bytes: &[u8], out: &mut PortableVector) {
    (
        out.elements[0],
        out.elements[1],
        out.elements[2],
        out.elements[3],
        out.elements[4],
        out.elements[5],
        out.elements[6],
        out.elements[7],
    ) = deserialize_11_int(&bytes[0..11]);
    (
        out.elements[8],
        out.elements[9],
        out.elements[10],
        out.elements[11],
        out.elements[12],
        out.elements[13],
        out.elements[14],
        out.elements[15],
    ) = deserialize_11_int(&bytes[11..22]);
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
     ${v.len() == 2}
"#))]
pub(crate) fn serialize_12_int(v: &[i16]) -> (u8, u8, u8) {
    let r0 = (v[0] & 0xFF) as u8;
    let r1 = ((v[0] >> 8) | ((v[1] & 0x0F) << 4)) as u8;
    let r2 = ((v[1] >> 4) & 0xFF) as u8;
    (r0, r1, r2)
}

#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--compat_pre_core 2 --z3rlimit 300 --z3refresh\"

let serialize_12_bit_vec_lemma (v: t_Array i16 (sz 16))
  (_: squash (forall i. Rust_primitives.bounded (Seq.index v i) 12))
   : squash (
     let inputs = bit_vec_of_int_t_array v 12 in
     let outputs = bit_vec_of_int_t_array (${serialize_12} ({ f_elements = v })) 8 in
     (forall (i: nat {i < 192}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options
"
    )
)]
#[cfg_attr(hax, hax_lib::fstar::after(interface, "
val serialize_12_lemma (inputs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) : Lemma
  (requires (forall i. Rust_primitives.bounded (Seq.index inputs.f_elements i) 12)) 
  (ensures bit_vec_of_int_t_array (${serialize_12} inputs) 8 == bit_vec_of_int_t_array inputs.f_elements 12)
"))]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--z3rlimit 300\"

let serialize_12_lemma inputs =
  serialize_12_bit_vec_lemma inputs.f_elements ();
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (${serialize_12} inputs) 8) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs.f_elements 12))

#pop-options
"
    )
)]
#[inline(always)]
pub(crate) fn serialize_12(v: PortableVector, out: &mut [u8]) {
    debug_assert!(out.len() == 24);
    (out[0], out[1], out[2]) = serialize_12_int(&v.elements[0..2]);
    (out[3], out[4], out[5]) = serialize_12_int(&v.elements[2..4]);
    (out[6], out[7], out[8]) = serialize_12_int(&v.elements[4..6]);
    (out[9], out[10], out[11]) = serialize_12_int(&v.elements[6..8]);
    (out[12], out[13], out[14]) = serialize_12_int(&v.elements[8..10]);
    (out[15], out[16], out[17]) = serialize_12_int(&v.elements[10..12]);
    (out[18], out[19], out[20]) = serialize_12_int(&v.elements[12..14]);
    (out[21], out[22], out[23]) = serialize_12_int(&v.elements[14..16]);
}

#[inline(always)]
#[hax_lib::requires(fstar!(r#"
     ${bytes.len() == 3}
"#))]
pub(crate) fn deserialize_12_int(bytes: &[u8]) -> (i16, i16) {
    let byte0 = bytes[0] as i16;
    let byte1 = bytes[1] as i16;
    let byte2 = bytes[2] as i16;
    let r0 = (byte1 & 0x0F) << 8 | (byte0 & 0xFF);
    let r1 = (byte2 << 4) | ((byte1 >> 4) & 0x0F);
    (r0, r1)
}

//deserialize_12_bounded_lemma
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        interface,
        "
val deserialize_12_bounded_lemma (inputs: t_Array u8 (sz 24)) : Lemma
  (ensures forall i. i < 16 ==> bounded (Seq.index (${deserialize_12} inputs).f_elements i) 12)
"
    )
)]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
let deserialize_12_bounded_lemma inputs =
  admit()
"
    )
)]
//deserialize_12_bit_vec_lemma
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--compat_pre_core 2 --z3rlimit 300 --z3refresh\"

let deserialize_12_bit_vec_lemma (v: t_Array u8 (sz 24))
   : squash (
     let inputs = bit_vec_of_int_t_array v 8 in
     let outputs = bit_vec_of_int_t_array (${deserialize_12} v).f_elements 12 in
     (forall (i: nat {i < 192}). inputs i == outputs i)
   ) =
  _ by (Tactics.GetBit.prove_bit_vector_equality' ())

#pop-options
"
    )
)]
//deserialize_12_lemma
#[cfg_attr(hax, hax_lib::fstar::after(interface, "
val deserialize_12_lemma (inputs: t_Array u8 (sz 24)) : Lemma
  (ensures bit_vec_of_int_t_array (${deserialize_12} inputs).f_elements 12 == bit_vec_of_int_t_array inputs 8)
"))]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        "
#push-options \"--z3rlimit 300\"

let deserialize_12_lemma inputs =
  deserialize_12_bit_vec_lemma inputs;
  BitVecEq.bit_vec_equal_intro (bit_vec_of_int_t_array (${deserialize_12} inputs).f_elements 12) 
    (BitVecEq.retype (bit_vec_of_int_t_array inputs 8))

#pop-options
"
    )
)]
#[hax_lib::requires(fstar!(r#"
     ${bytes.len() == 24}
"#))]
#[inline(always)]
pub(crate) fn deserialize_12(bytes: &[u8], out: &mut PortableVector) {
    (out.elements[0], out.elements[1]) = deserialize_12_int(&bytes[0..3]);
    (out.elements[2], out.elements[3]) = deserialize_12_int(&bytes[3..6]);
    (out.elements[4], out.elements[5]) = deserialize_12_int(&bytes[6..9]);
    (out.elements[6], out.elements[7]) = deserialize_12_int(&bytes[9..12]);
    (out.elements[8], out.elements[9]) = deserialize_12_int(&bytes[12..15]);
    (out.elements[10], out.elements[11]) = deserialize_12_int(&bytes[15..18]);
    (out.elements[12], out.elements[13]) = deserialize_12_int(&bytes[18..21]);
    (out.elements[14], out.elements[15]) = deserialize_12_int(&bytes[21..24]);
}
