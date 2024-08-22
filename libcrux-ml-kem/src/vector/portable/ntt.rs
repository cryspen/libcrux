use super::arithmetic::*;
use super::vector_type::*;

#[inline(always)]
pub(crate) fn ntt_step(v: &mut PortableVector, zeta: i16, i: usize, j: usize) {
    let t = montgomery_multiply_fe_by_fer(v.elements[j], zeta);
    v.elements[j] = v.elements[i] - t;
    v.elements[i] = v.elements[i] + t;
}

#[inline(always)]
pub(crate) fn ntt_layer_1_step(
    mut v: PortableVector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> PortableVector {
    ntt_step(&mut v, zeta0, 0, 2);
    ntt_step(&mut v, zeta0, 1, 3);
    ntt_step(&mut v, zeta1, 4, 6);
    ntt_step(&mut v, zeta1, 5, 7);
    ntt_step(&mut v, zeta2, 8, 10);
    ntt_step(&mut v, zeta2, 9, 11);
    ntt_step(&mut v, zeta3, 12, 14);
    ntt_step(&mut v, zeta3, 13, 15);
    v
}

#[inline(always)]
pub(crate) fn ntt_layer_2_step(mut v: PortableVector, zeta0: i16, zeta1: i16) -> PortableVector {
    ntt_step(&mut v, zeta0, 0, 4);
    ntt_step(&mut v, zeta0, 1, 5);
    ntt_step(&mut v, zeta0, 2, 6);
    ntt_step(&mut v, zeta0, 3, 7);
    ntt_step(&mut v, zeta1, 8, 12);
    ntt_step(&mut v, zeta1, 9, 13);
    ntt_step(&mut v, zeta1, 10, 14);
    ntt_step(&mut v, zeta1, 11, 15);
    v
}

#[inline(always)]
pub(crate) fn ntt_layer_3_step(mut v: PortableVector, zeta: i16) -> PortableVector {
    ntt_step(&mut v, zeta, 0, 8);
    ntt_step(&mut v, zeta, 1, 9);
    ntt_step(&mut v, zeta, 2, 10);
    ntt_step(&mut v, zeta, 3, 11);
    ntt_step(&mut v, zeta, 4, 12);
    ntt_step(&mut v, zeta, 5, 13);
    ntt_step(&mut v, zeta, 6, 14);
    ntt_step(&mut v, zeta, 7, 15);
    v
}

#[inline(always)]
pub(crate) fn inv_ntt_step(v: &mut PortableVector, zeta: i16, i: usize, j: usize) {
    let a_minus_b = v.elements[j] - v.elements[i];
    v.elements[i] = barrett_reduce_element(v.elements[i] + v.elements[j]);
    v.elements[j] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_1_step(
    mut v: PortableVector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> PortableVector {
    inv_ntt_step(&mut v, zeta0, 0, 2);
    inv_ntt_step(&mut v, zeta0, 1, 3);
    inv_ntt_step(&mut v, zeta1, 4, 6);
    inv_ntt_step(&mut v, zeta1, 5, 7);
    inv_ntt_step(&mut v, zeta2, 8, 10);
    inv_ntt_step(&mut v, zeta2, 9, 11);
    inv_ntt_step(&mut v, zeta3, 12, 14);
    inv_ntt_step(&mut v, zeta3, 13, 15);
    v
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_2_step(
    mut v: PortableVector,
    zeta0: i16,
    zeta1: i16,
) -> PortableVector {
    inv_ntt_step(&mut v, zeta0, 0, 4);
    inv_ntt_step(&mut v, zeta0, 1, 5);
    inv_ntt_step(&mut v, zeta0, 2, 6);
    inv_ntt_step(&mut v, zeta0, 3, 7);
    inv_ntt_step(&mut v, zeta1, 8, 12);
    inv_ntt_step(&mut v, zeta1, 9, 13);
    inv_ntt_step(&mut v, zeta1, 10, 14);
    inv_ntt_step(&mut v, zeta1, 11, 15);
    v
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_3_step(mut v: PortableVector, zeta: i16) -> PortableVector {
    inv_ntt_step(&mut v, zeta, 0, 8);
    inv_ntt_step(&mut v, zeta, 1, 9);
    inv_ntt_step(&mut v, zeta, 2, 10);
    inv_ntt_step(&mut v, zeta, 3, 11);
    inv_ntt_step(&mut v, zeta, 4, 12);
    inv_ntt_step(&mut v, zeta, 5, 13);
    inv_ntt_step(&mut v, zeta, 6, 14);
    inv_ntt_step(&mut v, zeta, 7, 15);
    v
}

/// Compute the product of two Kyber binomials with respect to the
/// modulus `X² - zeta`.
///
/// This function almost implements <strong>Algorithm 11</strong> of the
/// NIST FIPS 203 standard, which is reproduced below:
///
/// ```plaintext
/// Input:  a₀, a₁, b₀, b₁ ∈ ℤq.
/// Input: γ ∈ ℤq.
/// Output: c₀, c₁ ∈ ℤq.
///
/// c₀ ← a₀·b₀ + a₁·b₁·γ
/// c₁ ← a₀·b₁ + a₁·b₀
/// return c₀, c₁
/// ```
/// We say "almost" because the coefficients output by this function are in
/// the Montgomery domain (unlike in the specification).
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
#[inline(always)]
pub(crate) fn ntt_multiply_binomials(
    a: &PortableVector,
    b: &PortableVector,
    zeta: FieldElementTimesMontgomeryR,
    i: usize,
    j: usize,
    out: &mut PortableVector,
) {
    let o0 = montgomery_reduce_element(
        (a.elements[i] as i32) * (b.elements[i] as i32)
            + (montgomery_reduce_element((a.elements[j] as i32) * (b.elements[j] as i32)) as i32)
                * (zeta as i32),
    );
    let o1 = montgomery_reduce_element(
        (a.elements[i] as i32) * (b.elements[j] as i32)
            + (a.elements[j] as i32) * (b.elements[i] as i32),
    );
    out.elements[i] = o0;
    out.elements[j] = o1;
}

// #[inline(always)]
// pub(crate) fn ntt_multiply_binomials(
//     (a0, a1): (FieldElement, FieldElement),
//     (b0, b1): (FieldElement, FieldElement),
//     zeta: FieldElementTimesMontgomeryR,
// ) -> (MontgomeryFieldElement, MontgomeryFieldElement) {
//     (
//         montgomery_reduce_element(
//             (a0 as i32) * (b0 as i32)
//                 + (montgomery_reduce_element((a1 as i32) * (b1 as i32)) as i32) * (zeta as i32),
//         ),
//         montgomery_reduce_element((a0 as i32) * (b1 as i32) + (a1 as i32) * (b0 as i32)),
//     )
// }

#[inline(always)]
pub(crate) fn ntt_multiply(
    lhs: &PortableVector,
    rhs: &PortableVector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> PortableVector {
    let mut out = zero();
    ntt_multiply_binomials(lhs, rhs, zeta0, 0, 1, &mut out);
    ntt_multiply_binomials(lhs, rhs, -zeta0, 2, 3, &mut out);
    ntt_multiply_binomials(lhs, rhs, zeta1, 4, 5, &mut out);
    ntt_multiply_binomials(lhs, rhs, -zeta1, 6, 7, &mut out);
    ntt_multiply_binomials(lhs, rhs, zeta2, 8, 9, &mut out);
    ntt_multiply_binomials(lhs, rhs, -zeta2, 10, 11, &mut out);
    ntt_multiply_binomials(lhs, rhs, zeta3, 12, 13, &mut out);
    ntt_multiply_binomials(lhs, rhs, -zeta3, 14, 15, &mut out);
    out
}
