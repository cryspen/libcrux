use super::{
    arithmetic::{
        add_to_ring_element, barrett_reduce, montgomery_reduce, KyberFieldElement,
        KyberPolynomialRingElement,
    },
    constants::{COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS},
};

const ZETAS_MONTGOMERY_DOMAIN: [KyberFieldElement; 128] = [
    -1044, -758, -359, -1517, 1493, 1422, 287, 202, -171, 622, 1577, 182, 962, -1202, -1474, 1468,
    573, -1325, 264, 383, -829, 1458, -1602, -130, -681, 1017, 732, 608, -1542, 411, -205, -1571,
    1223, 652, -552, 1015, -1293, 1491, -282, -1544, 516, -8, -320, -666, -1618, -1162, 126, 1469,
    -853, -90, -271, 830, 107, -1421, -247, -951, -398, 961, -1508, -725, 448, -1065, 677, -1275,
    -1103, 430, 555, 843, -1251, 871, 1550, 105, 422, 587, 177, -235, -291, -460, 1574, 1653, -246,
    778, 1159, -147, -777, 1483, -602, 1119, -1590, 644, -872, 349, 418, 329, -156, -75, 817, 1097,
    603, 610, 1322, -1285, -1465, 384, -1215, -136, 1218, -1335, -874, 220, -1187, -1659, -1185,
    -1530, -1278, 794, -1510, -854, -870, 478, -108, -308, 996, 991, 958, -1460, 1522, 1628,
];

macro_rules! ntt_at_layer {
    ($layer:literal, $zeta_i:ident, $re:ident, $initial_coefficient_bound:literal) => {
        let layer_jump = 1 << $layer;
        for offset in (0..(COEFFICIENTS_IN_RING_ELEMENT - layer_jump)).step_by(2 * layer_jump) {
            $zeta_i += 1;

            for j in offset..offset + layer_jump {
                let t = montgomery_reduce(
                    $re.coefficients[j + layer_jump] * ZETAS_MONTGOMERY_DOMAIN[$zeta_i],
                );
                $re.coefficients[j + layer_jump] = $re.coefficients[j] - t;
                $re.coefficients[j] = $re.coefficients[j] + t;
            }
        }

        debug_assert!($re.coefficients.into_iter().all(|coefficient| {
            coefficient.abs()
                < $initial_coefficient_bound + ((8 - $layer) * 3 * (FIELD_MODULUS / 2))
        }));
    };
}

// Over time, all invocations of ntt_representation() will be replaced by
// invocations to this function, upon which this function will be renamed back to
// ntt_representation().
#[inline(always)]
pub(in crate::kem::kyber) fn ntt_binomially_sampled_ring_element(
    mut re: KyberPolynomialRingElement,
) -> KyberPolynomialRingElement {
    debug_assert!(re
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient.abs() <= 3));

    let mut zeta_i = 0;

    // This function is only being used in key-generation for the moment, and we
    // can skip the first round of montgomery reductions for the ring elements
    // being passed in during key-generation.
    for offset in (0..(COEFFICIENTS_IN_RING_ELEMENT - 128)).step_by(2 * 128) {
        zeta_i += 1;

        for j in offset..offset + 128 {
            // Multiply by the appropriate zeta in the normal domain.
            let t = re.coefficients[j + 128] * -1600;

            re.coefficients[j + 128] = re.coefficients[j] - t;
            re.coefficients[j] = re.coefficients[j] + t;
        }
    }
    debug_assert!(re
        .coefficients
        .into_iter()
        .all(|coefficient| { coefficient.abs() < 3 + (3 * (FIELD_MODULUS / 2)) }));

    ntt_at_layer!(6, zeta_i, re, 3);
    ntt_at_layer!(5, zeta_i, re, 3);
    ntt_at_layer!(4, zeta_i, re, 3);
    ntt_at_layer!(3, zeta_i, re, 3);
    ntt_at_layer!(2, zeta_i, re, 3);
    ntt_at_layer!(1, zeta_i, re, 3);

    re.coefficients = re.coefficients.map(barrett_reduce);

    re
}

#[inline(always)]
pub(in crate::kem::kyber) fn ntt_vector_u<const VECTOR_U_COMPRESSION_FACTOR: usize>(
    mut re: KyberPolynomialRingElement,
) -> KyberPolynomialRingElement {
    debug_assert!(re
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient.abs() <= 3328));

    let mut zeta_i = 0;

    ntt_at_layer!(7, zeta_i, re, 3328);
    ntt_at_layer!(6, zeta_i, re, 3328);
    ntt_at_layer!(5, zeta_i, re, 3328);
    ntt_at_layer!(4, zeta_i, re, 3328);
    ntt_at_layer!(3, zeta_i, re, 3328);
    ntt_at_layer!(2, zeta_i, re, 3328);
    ntt_at_layer!(1, zeta_i, re, 3328);

    re.coefficients = re.coefficients.map(barrett_reduce);

    re
}

#[inline(always)]
fn invert_ntt_montgomery<const K: usize>(
    mut re: KyberPolynomialRingElement,
) -> KyberPolynomialRingElement {
    // We only ever call this function after matrix/vector multiplication
    debug_assert!(re
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient.abs() < (K as i32) * FIELD_MODULUS));

    let mut zeta_i = COEFFICIENTS_IN_RING_ELEMENT / 2;

    macro_rules! invert_ntt_at_layer {
        ($layer:literal) => {
            for offset in (0..(COEFFICIENTS_IN_RING_ELEMENT - $layer)).step_by(2 * $layer) {
                zeta_i -= 1;

                for j in offset..offset + $layer {
                    let a_minus_b = re.coefficients[j + $layer] - re.coefficients[j];

                    // Instead of dividing by 2 here, we just divide by
                    // 2^7 in one go in the end.
                    re.coefficients[j] = re.coefficients[j] + re.coefficients[j + $layer];
                    re.coefficients[j + $layer] =
                        montgomery_reduce(a_minus_b * ZETAS_MONTGOMERY_DOMAIN[zeta_i]);
                }
            }
        };
    }

    invert_ntt_at_layer!(2);
    invert_ntt_at_layer!(4);
    invert_ntt_at_layer!(8);
    invert_ntt_at_layer!(16);
    invert_ntt_at_layer!(32);
    invert_ntt_at_layer!(64);
    invert_ntt_at_layer!(128);

    macro_rules! bound_for_set_coefficients {
        ($parameter:literal) => {
            debug_assert!(re
                .coefficients
                .into_iter()
                .skip($parameter)
                .take($parameter)
                .all(|coefficient| coefficient.abs() < (128 / $parameter) * FIELD_MODULUS));
        };
    }

    debug_assert!(
        re.coefficients[0].abs() < 128 * (K as i32) * FIELD_MODULUS
            && re.coefficients[1].abs() < 128 * (K as i32) * FIELD_MODULUS
    );
    bound_for_set_coefficients!(2);
    bound_for_set_coefficients!(4);
    bound_for_set_coefficients!(8);
    bound_for_set_coefficients!(16);
    bound_for_set_coefficients!(32);
    bound_for_set_coefficients!(64);
    bound_for_set_coefficients!(128);

    for i in 0..8 {
        re.coefficients[i] = barrett_reduce(re.coefficients[i]);
    }
    re
}

#[inline(always)]
fn ntt_multiply_binomials(
    (a0, a1): (KyberFieldElement, KyberFieldElement),
    (b0, b1): (KyberFieldElement, KyberFieldElement),
    zeta: i32,
) -> (KyberFieldElement, KyberFieldElement) {
    (
        montgomery_reduce(a0 * b0 + montgomery_reduce(a1 * b1) * zeta),
        montgomery_reduce(a0 * b1 + a1 * b0),
    )
}

#[inline(always)]
fn ntt_multiply(
    left: &KyberPolynomialRingElement,
    right: &KyberPolynomialRingElement,
) -> KyberPolynomialRingElement {
    debug_assert!(left
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient >= 0 && coefficient < 4096));
    debug_assert!(right
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient > -FIELD_MODULUS && coefficient < FIELD_MODULUS));

    let mut out = KyberPolynomialRingElement::ZERO;

    for i in (0..COEFFICIENTS_IN_RING_ELEMENT).step_by(4) {
        let product = ntt_multiply_binomials(
            (left.coefficients[i], left.coefficients[i + 1]),
            (right.coefficients[i], right.coefficients[i + 1]),
            ZETAS_MONTGOMERY_DOMAIN[64 + (i / 4)],
        );
        out.coefficients[i] = product.0;
        out.coefficients[i + 1] = product.1;

        let product = ntt_multiply_binomials(
            (left.coefficients[i + 2], left.coefficients[i + 3]),
            (right.coefficients[i + 2], right.coefficients[i + 3]),
            -ZETAS_MONTGOMERY_DOMAIN[64 + (i / 4)],
        );
        out.coefficients[i + 2] = product.0;
        out.coefficients[i + 3] = product.1;
    }

    debug_assert!(out
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient > -FIELD_MODULUS && coefficient < FIELD_MODULUS));

    out
}

// v := NTT^{−1}(tˆT ◦ rˆ) + e_2 + Decompress_q(Decode_1(m),1)
#[inline(always)]
pub(in crate::kem::kyber) fn compute_message<const K: usize>(
    v: &KyberPolynomialRingElement,
    secret_as_ntt: &[KyberPolynomialRingElement; K],
    u_as_ntt: &[KyberPolynomialRingElement; K],
) -> KyberPolynomialRingElement {
    let mut result = KyberPolynomialRingElement::ZERO;

    for (secret_element, u_element) in secret_as_ntt.iter().zip(u_as_ntt.iter()) {
        let product = ntt_multiply(secret_element, u_element);
        result = add_to_ring_element(result, &product);
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

    for (t_element, r_element) in t_as_ntt.iter().zip(r_as_ntt.iter()) {
        let product = ntt_multiply(t_element, r_element);
        result = add_to_ring_element(result, &product);
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
            result[i] = add_to_ring_element(result[i], &product);
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

// NOTE: This function performs matrix multiplication, then conversion from the
// montgomery domain, and last barrett reduction. It is only used in
// ind_cpa::generate_keypair(). (TODO: Verify this) Doing barrett reduction in
// this function after conversion from montgomery form lets us skip an extra
// barrett reduction step in generate_keypair itself.
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
            result[i] = add_to_ring_element(result[i], &product);
        }

        debug_assert!(result[i]
            .coefficients
            .into_iter()
            .all(|coefficient| coefficient.abs() < (K as i32) * FIELD_MODULUS));

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
