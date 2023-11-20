use super::{
    arithmetic::{
        add_to_ring_element, barrett_reduce, montgomery_reduce, KyberPolynomialRingElement,
    },
    ntt::{invert_ntt_montgomery, ntt_multiply},
};

#[inline(always)]
pub(in crate::kem::kyber) fn compute_message<const K: usize>(
    v: &KyberPolynomialRingElement,
    secret_as_ntt: &[KyberPolynomialRingElement; K],
    u_as_ntt: &[KyberPolynomialRingElement; K],
) -> KyberPolynomialRingElement {
    let mut result = KyberPolynomialRingElement::ZERO;

    for i in 0..K {
        let product = ntt_multiply(&secret_as_ntt[i], &u_as_ntt[i]);
        result = add_to_ring_element::<K>(result, &product);
    }

    result = invert_ntt_montgomery::<K>(result);

    for i in 0..result.coefficients.len() {
        let coefficient_normal_form = montgomery_reduce(result.coefficients[i] * 1441);
        result.coefficients[i] = barrett_reduce(v.coefficients[i] - coefficient_normal_form);
    }

    result
}

// v := NTT^{−1}(tˆT ◦ rˆ) + e_2 + Decompress_q(Decode_1(m),1)
#[inline(always)]
pub(in crate::kem::kyber) fn compute_ring_element_v<const K: usize>(
    t_as_ntt: &[KyberPolynomialRingElement; K],
    r_as_ntt: &[KyberPolynomialRingElement; K],
    error_2: &KyberPolynomialRingElement,
    message: &KyberPolynomialRingElement,
) -> KyberPolynomialRingElement {
    let mut result = KyberPolynomialRingElement::ZERO;

    for i in 0..K {
        let product = ntt_multiply(&t_as_ntt[i], &r_as_ntt[i]);
        result = add_to_ring_element::<K>(result, &product);
    }

    result = invert_ntt_montgomery::<K>(result);

    for i in 0..result.coefficients.len() {
        let coefficient_normal_form = montgomery_reduce(result.coefficients[i] * 1441);
        result.coefficients[i] = barrett_reduce(
            coefficient_normal_form + error_2.coefficients[i] + message.coefficients[i],
        );
    }

    result
}

// u := NTT^{-1}(AˆT ◦ rˆ) + e_1
#[inline(always)]
pub(in crate::kem::kyber) fn compute_vector_u<const K: usize>(
    a_as_ntt: &[[KyberPolynomialRingElement; K]; K],
    r_as_ntt: &[KyberPolynomialRingElement; K],
    error_1: &[KyberPolynomialRingElement; K],
) -> [KyberPolynomialRingElement; K] {
    let mut result = [KyberPolynomialRingElement::ZERO; K];

    for (i, row) in a_as_ntt.iter().enumerate() {
        for (j, a_element) in row.iter().enumerate() {
            let product = ntt_multiply(a_element, &r_as_ntt[j]);
            result[i] = add_to_ring_element::<K>(result[i], &product);
        }

        result[i] = invert_ntt_montgomery::<K>(result[i]);

        for j in 0..result[i].coefficients.len() {
            let coefficient_normal_form = montgomery_reduce(result[i].coefficients[j] * 1441);

            result[i].coefficients[j] =
                barrett_reduce(coefficient_normal_form + error_1[i].coefficients[j]);
        }
    }

    result
}

#[inline(always)]
#[allow(non_snake_case)]
pub(in crate::kem::kyber) fn compute_As_plus_e<const K: usize>(
    matrix_A: &[[KyberPolynomialRingElement; K]; K],
    s_as_ntt: &[KyberPolynomialRingElement; K],
    error_as_ntt: &[KyberPolynomialRingElement; K],
) -> [KyberPolynomialRingElement; K] {
    let mut result = [KyberPolynomialRingElement::ZERO; K];

    for (i, row) in matrix_A.iter().enumerate() {
        for (j, matrix_element) in row.iter().enumerate() {
            let product = ntt_multiply(matrix_element, &s_as_ntt[j]);
            result[i] = add_to_ring_element::<K>(result[i], &product);
        }

        for j in 0..result[i].coefficients.len() {
            // The coefficients are of the form aR^{-1} mod q, which means
            // calling to_montgomery_domain() on them should return a mod q.
            let coefficient_normal_form = montgomery_reduce(result[i].coefficients[j] * 1353);

            result[i].coefficients[j] =
                barrett_reduce(coefficient_normal_form + error_as_ntt[i].coefficients[j])
        }
    }

    result
}
