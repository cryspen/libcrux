use super::arithmetic::*;
use super::vector_type::*;

#[inline(always)]
pub(crate) fn ntt_layer_1_step(
    mut v: PortableVector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> PortableVector {
    // First 8 elements.
    let t = montgomery_multiply_fe_by_fer(v.elements[2], zeta0);
    v.elements[2] = v.elements[0] - t;
    v.elements[0] = v.elements[0] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[3], zeta0);
    v.elements[3] = v.elements[1] - t;
    v.elements[1] = v.elements[1] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[6], zeta1);
    v.elements[6] = v.elements[4] - t;
    v.elements[4] = v.elements[4] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[7], zeta1);
    v.elements[7] = v.elements[5] - t;
    v.elements[5] = v.elements[5] + t;

    // Next 8 elements.
    let t = montgomery_multiply_fe_by_fer(v.elements[8 + 2], zeta2);
    v.elements[8 + 2] = v.elements[8 + 0] - t;
    v.elements[8 + 0] = v.elements[8 + 0] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[8 + 3], zeta2);
    v.elements[8 + 3] = v.elements[8 + 1] - t;
    v.elements[8 + 1] = v.elements[8 + 1] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[8 + 6], zeta3);
    v.elements[8 + 6] = v.elements[8 + 4] - t;
    v.elements[8 + 4] = v.elements[8 + 4] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[8 + 7], zeta3);
    v.elements[8 + 7] = v.elements[8 + 5] - t;
    v.elements[8 + 5] = v.elements[8 + 5] + t;

    v
}

#[inline(always)]
pub(crate) fn ntt_layer_3_step(mut v: PortableVector, zeta: i16) -> PortableVector {
    let t = montgomery_multiply_fe_by_fer(v.elements[8], zeta);
    v.elements[8] = v.elements[0] - t;
    v.elements[0] = v.elements[0] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[9], zeta);
    v.elements[9] = v.elements[1] - t;
    v.elements[1] = v.elements[1] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[10], zeta);
    v.elements[10] = v.elements[2] - t;
    v.elements[2] = v.elements[2] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[11], zeta);
    v.elements[11] = v.elements[3] - t;
    v.elements[3] = v.elements[3] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[12], zeta);
    v.elements[12] = v.elements[4] - t;
    v.elements[4] = v.elements[4] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[13], zeta);
    v.elements[13] = v.elements[5] - t;
    v.elements[5] = v.elements[5] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[14], zeta);
    v.elements[14] = v.elements[6] - t;
    v.elements[6] = v.elements[6] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[15], zeta);
    v.elements[15] = v.elements[7] - t;
    v.elements[7] = v.elements[7] + t;

    v
}

#[inline(always)]
pub(crate) fn ntt_layer_2_step(mut v: PortableVector, zeta0: i16, zeta1: i16) -> PortableVector {
    // First 8 elements.
    let t = montgomery_multiply_fe_by_fer(v.elements[4], zeta0);
    v.elements[4] = v.elements[0] - t;
    v.elements[0] = v.elements[0] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[5], zeta0);
    v.elements[5] = v.elements[1] - t;
    v.elements[1] = v.elements[1] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[6], zeta0);
    v.elements[6] = v.elements[2] - t;
    v.elements[2] = v.elements[2] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[7], zeta0);
    v.elements[7] = v.elements[3] - t;
    v.elements[3] = v.elements[3] + t;

    // Next 8 elements.
    let t = montgomery_multiply_fe_by_fer(v.elements[8 + 4], zeta1);
    v.elements[8 + 4] = v.elements[8 + 0] - t;
    v.elements[8 + 0] = v.elements[8 + 0] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[8 + 5], zeta1);
    v.elements[8 + 5] = v.elements[8 + 1] - t;
    v.elements[8 + 1] = v.elements[8 + 1] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[8 + 6], zeta1);
    v.elements[8 + 6] = v.elements[8 + 2] - t;
    v.elements[8 + 2] = v.elements[8 + 2] + t;

    let t = montgomery_multiply_fe_by_fer(v.elements[8 + 7], zeta1);
    v.elements[8 + 7] = v.elements[8 + 3] - t;
    v.elements[8 + 3] = v.elements[8 + 3] + t;

    v
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_1_step(
    mut v: PortableVector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> PortableVector {
    // First 8 elements.
    let a_minus_b = v.elements[2] - v.elements[0];
    v.elements[0] = barrett_reduce_element(v.elements[0] + v.elements[2]);
    v.elements[2] = montgomery_multiply_fe_by_fer(a_minus_b, zeta0);

    let a_minus_b = v.elements[3] - v.elements[1];
    v.elements[1] = barrett_reduce_element(v.elements[1] + v.elements[3]);
    v.elements[3] = montgomery_multiply_fe_by_fer(a_minus_b, zeta0);

    let a_minus_b = v.elements[6] - v.elements[4];
    v.elements[4] = barrett_reduce_element(v.elements[4] + v.elements[6]);
    v.elements[6] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

    let a_minus_b = v.elements[7] - v.elements[5];
    v.elements[5] = barrett_reduce_element(v.elements[5] + v.elements[7]);
    v.elements[7] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

    // Next 8 elements.
    let a_minus_b = v.elements[8 + 2] - v.elements[8 + 0];
    v.elements[8 + 0] = barrett_reduce_element(v.elements[8 + 0] + v.elements[8 + 2]);
    v.elements[8 + 2] = montgomery_multiply_fe_by_fer(a_minus_b, zeta2);

    let a_minus_b = v.elements[8 + 3] - v.elements[8 + 1];
    v.elements[8 + 1] = barrett_reduce_element(v.elements[8 + 1] + v.elements[8 + 3]);
    v.elements[8 + 3] = montgomery_multiply_fe_by_fer(a_minus_b, zeta2);

    let a_minus_b = v.elements[8 + 6] - v.elements[8 + 4];
    v.elements[8 + 4] = barrett_reduce_element(v.elements[8 + 4] + v.elements[8 + 6]);
    v.elements[8 + 6] = montgomery_multiply_fe_by_fer(a_minus_b, zeta3);

    let a_minus_b = v.elements[8 + 7] - v.elements[8 + 5];
    v.elements[8 + 5] = barrett_reduce_element(v.elements[8 + 5] + v.elements[8 + 7]);
    v.elements[8 + 7] = montgomery_multiply_fe_by_fer(a_minus_b, zeta3);

    v
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_2_step(
    mut v: PortableVector,
    zeta0: i16,
    zeta1: i16,
) -> PortableVector {
    // First 8 elements.
    let a_minus_b = v.elements[4] - v.elements[0];
    v.elements[0] = v.elements[0] + v.elements[4];
    v.elements[4] = montgomery_multiply_fe_by_fer(a_minus_b, zeta0);

    let a_minus_b = v.elements[5] - v.elements[1];
    v.elements[1] = v.elements[1] + v.elements[5];
    v.elements[5] = montgomery_multiply_fe_by_fer(a_minus_b, zeta0);

    let a_minus_b = v.elements[6] - v.elements[2];
    v.elements[2] = v.elements[2] + v.elements[6];
    v.elements[6] = montgomery_multiply_fe_by_fer(a_minus_b, zeta0);

    let a_minus_b = v.elements[7] - v.elements[3];
    v.elements[3] = v.elements[3] + v.elements[7];
    v.elements[7] = montgomery_multiply_fe_by_fer(a_minus_b, zeta0);

    // Next 8 elements.
    let a_minus_b = v.elements[8 + 4] - v.elements[8 + 0];
    v.elements[8 + 0] = v.elements[8 + 0] + v.elements[8 + 4];
    v.elements[8 + 4] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

    let a_minus_b = v.elements[8 + 5] - v.elements[8 + 1];
    v.elements[8 + 1] = v.elements[8 + 1] + v.elements[8 + 5];
    v.elements[8 + 5] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

    let a_minus_b = v.elements[8 + 6] - v.elements[8 + 2];
    v.elements[8 + 2] = v.elements[8 + 2] + v.elements[8 + 6];
    v.elements[8 + 6] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

    let a_minus_b = v.elements[8 + 7] - v.elements[8 + 3];
    v.elements[8 + 3] = v.elements[8 + 3] + v.elements[8 + 7];
    v.elements[8 + 7] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

    v
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_3_step(mut v: PortableVector, zeta: i16) -> PortableVector {
    let a_minus_b = v.elements[8] - v.elements[0];
    v.elements[0] = v.elements[0] + v.elements[8];
    v.elements[8] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = v.elements[9] - v.elements[1];
    v.elements[1] = v.elements[1] + v.elements[9];
    v.elements[9] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = v.elements[10] - v.elements[2];
    v.elements[2] = v.elements[2] + v.elements[10];
    v.elements[10] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = v.elements[11] - v.elements[3];
    v.elements[3] = v.elements[3] + v.elements[11];
    v.elements[11] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = v.elements[12] - v.elements[4];
    v.elements[4] = v.elements[4] + v.elements[12];
    v.elements[12] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = v.elements[13] - v.elements[5];
    v.elements[5] = v.elements[5] + v.elements[13];
    v.elements[13] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = v.elements[14] - v.elements[6];
    v.elements[6] = v.elements[6] + v.elements[14];
    v.elements[14] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = v.elements[15] - v.elements[7];
    v.elements[7] = v.elements[7] + v.elements[15];
    v.elements[15] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

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
    (a0, a1): (FieldElement, FieldElement),
    (b0, b1): (FieldElement, FieldElement),
    zeta: FieldElementTimesMontgomeryR,
) -> (MontgomeryFieldElement, MontgomeryFieldElement) {
    (
        montgomery_reduce_element(
            (a0 as i32) * (b0 as i32)
                + (montgomery_reduce_element((a1 as i32) * (b1 as i32)) as i32) * (zeta as i32),
        ),
        montgomery_reduce_element((a0 as i32) * (b1 as i32) + (a1 as i32) * (b0 as i32)),
    )
}

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

    // First 8 elements.
    let product = ntt_multiply_binomials(
        (lhs.elements[0], lhs.elements[1]),
        (rhs.elements[0], rhs.elements[1]),
        zeta0,
    );
    out.elements[0] = product.0;
    out.elements[1] = product.1;

    let product = ntt_multiply_binomials(
        (lhs.elements[2], lhs.elements[3]),
        (rhs.elements[2], rhs.elements[3]),
        -zeta0,
    );
    out.elements[2] = product.0;
    out.elements[3] = product.1;

    let product = ntt_multiply_binomials(
        (lhs.elements[4], lhs.elements[5]),
        (rhs.elements[4], rhs.elements[5]),
        zeta1,
    );
    out.elements[4] = product.0;
    out.elements[5] = product.1;

    let product = ntt_multiply_binomials(
        (lhs.elements[6], lhs.elements[7]),
        (rhs.elements[6], rhs.elements[7]),
        -zeta1,
    );
    out.elements[6] = product.0;
    out.elements[7] = product.1;

    // Next 8 elements.
    let product = ntt_multiply_binomials(
        (lhs.elements[8 + 0], lhs.elements[8 + 1]),
        (rhs.elements[8 + 0], rhs.elements[8 + 1]),
        zeta2,
    );
    out.elements[8 + 0] = product.0;
    out.elements[8 + 1] = product.1;

    let product = ntt_multiply_binomials(
        (lhs.elements[8 + 2], lhs.elements[8 + 3]),
        (rhs.elements[8 + 2], rhs.elements[8 + 3]),
        -zeta2,
    );
    out.elements[8 + 2] = product.0;
    out.elements[8 + 3] = product.1;

    let product = ntt_multiply_binomials(
        (lhs.elements[8 + 4], lhs.elements[8 + 5]),
        (rhs.elements[8 + 4], rhs.elements[8 + 5]),
        zeta3,
    );
    out.elements[8 + 4] = product.0;
    out.elements[8 + 5] = product.1;

    let product = ntt_multiply_binomials(
        (lhs.elements[8 + 6], lhs.elements[8 + 7]),
        (rhs.elements[8 + 6], rhs.elements[8 + 7]),
        -zeta3,
    );
    out.elements[8 + 6] = product.0;
    out.elements[8 + 7] = product.1;

    out
}
