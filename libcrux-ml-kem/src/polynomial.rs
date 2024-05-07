use libcrux_polynomials::{
    FieldElementTimesMontgomeryR, GenericOperations, Operations, FIELD_ELEMENTS_IN_VECTOR,
};

pub(crate) const VECTORS_IN_RING_ELEMENT: usize =
    super::constants::COEFFICIENTS_IN_RING_ELEMENT / FIELD_ELEMENTS_IN_VECTOR;

use crate::hax_utils::hax_debug_assert;

#[derive(Clone, Copy)]
pub(crate) struct PolynomialRingElement<Vector: Operations> {
    pub(crate) coefficients: [Vector; VECTORS_IN_RING_ELEMENT],
}

impl<Vector: Operations> PolynomialRingElement<Vector> {
    #[allow(non_snake_case)]
    pub(crate) fn ZERO() -> Self {
        Self {
            // FIXME:  The THIR body of item DefId(0:415 ~ libcrux_ml_kem[9000]::polynomial::{impl#0}::ZERO::{constant#0}) was stolen.
            coefficients: [Vector::ZERO(); 16],
        }
    }

    #[inline(always)]
    pub(crate) fn from_i16_array(a: [i16; 256]) -> Self {
        let mut result = PolynomialRingElement::ZERO();
        for i in 0..VECTORS_IN_RING_ELEMENT {
            result.coefficients[i] = Vector::from_i16_array(
                a[i * FIELD_ELEMENTS_IN_VECTOR..(i + 1) * FIELD_ELEMENTS_IN_VECTOR]
                    .try_into()
                    .unwrap(),
            );
        }
        result
    }

    /// Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
    /// sum of their constituent coefficients.
    #[inline(always)]
    pub(crate) fn add_to_ring_element<const K: usize>(mut self, rhs: &Self) -> Self {
        for i in 0..self.coefficients.len() {
            self.coefficients[i] = Vector::add(self.coefficients[i], &rhs.coefficients[i]);
        }
        self
    }

    #[inline(always)]
    pub fn poly_barrett_reduce(mut self) -> Self {
        for i in 0..VECTORS_IN_RING_ELEMENT {
            self.coefficients[i] = Vector::barrett_reduce(self.coefficients[i]);
        }
        self
    }

    #[inline(always)]
    pub(crate) fn subtract_reduce(&self, mut b: Self) -> Self {
        for i in 0..VECTORS_IN_RING_ELEMENT {
            let coefficient_normal_form =
                Vector::montgomery_multiply_by_constant(b.coefficients[i], 1441);
            b.coefficients[i] =
                Vector::barrett_reduce(Vector::sub(self.coefficients[i], &coefficient_normal_form));
        }
        b
    }

    #[inline(always)]
    pub(crate) fn add_message_error_reduce(&self, message: &Self, mut result: Self) -> Self {
        for i in 0..VECTORS_IN_RING_ELEMENT {
            let coefficient_normal_form =
                Vector::montgomery_multiply_by_constant(result.coefficients[i], 1441);
            result.coefficients[i] = Vector::barrett_reduce(Vector::add(
                coefficient_normal_form,
                &Vector::add(self.coefficients[i], &message.coefficients[i]),
            ));
        }
        result
    }

    #[inline(always)]
    pub(crate) fn add_error_reduce(&self, mut result: Self) -> Self {
        for j in 0..VECTORS_IN_RING_ELEMENT {
            let coefficient_normal_form =
                Vector::montgomery_multiply_by_constant(result.coefficients[j], 1441);

            result.coefficients[j] =
                Vector::barrett_reduce(Vector::add(coefficient_normal_form, &self.coefficients[j]));
        }
        result
    }

    #[inline(always)]
    pub(crate) fn add_standard_error_reduce(&self, mut result: Self) -> Self {
        for j in 0..VECTORS_IN_RING_ELEMENT {
            // The coefficients are of the form aR^{-1} mod q, which means
            // calling to_montgomery_domain() on them should return a mod q.
            let coefficient_normal_form = Vector::to_standard_domain(result.coefficients[j]);

            result.coefficients[j] =
                Vector::barrett_reduce(Vector::add(coefficient_normal_form, &self.coefficients[j]));
        }
        result
    }

    /// Given two `KyberPolynomialRingElement`s in their NTT representations,
    /// compute their product. Given two polynomials in the NTT domain `f^` and `ĵ`,
    /// the `iᵗʰ` coefficient of the product `k̂` is determined by the calculation:
    ///
    /// ```plaintext
    /// ĥ[2·i] + ĥ[2·i + 1]X = (f^[2·i] + f^[2·i + 1]X)·(ĝ[2·i] + ĝ[2·i + 1]X) mod (X² - ζ^(2·BitRev₇(i) + 1))
    /// ```
    ///
    /// This function almost implements <strong>Algorithm 10</strong> of the
    /// NIST FIPS 203 standard, which is reproduced below:
    ///
    /// ```plaintext
    /// Input: Two arrays fˆ ∈ ℤ₂₅₆ and ĝ ∈ ℤ₂₅₆.
    /// Output: An array ĥ ∈ ℤq.
    ///
    /// for(i ← 0; i < 128; i++)
    ///     (ĥ[2i], ĥ[2i+1]) ← BaseCaseMultiply(fˆ[2i], fˆ[2i+1], ĝ[2i], ĝ[2i+1], ζ^(2·BitRev₇(i) + 1))
    /// end for
    /// return ĥ
    /// ```
    /// We say "almost" because the coefficients of the ring element output by
    /// this function are in the Montgomery domain.
    ///
    /// The NIST FIPS 203 standard can be found at
    /// <https://csrc.nist.gov/pubs/fips/203/ipd>.
    // TODO: Remove or replace with something that works and is useful for the proof.
    // #[cfg_attr(hax, hax_lib::requires(
    //     hax_lib::forall(|i:usize|
    //         hax_lib::implies(i < COEFFICIENTS_IN_RING_ELEMENT, ||
    //             (lhs.coefficients[i] >= 0 && lhs.coefficients[i] < 4096) &&
    //             (rhs.coefficients[i].abs() <= FIELD_MODULUS)

    // ))))]
    // #[cfg_attr(hax, hax_lib::ensures(|result|
    //     hax_lib::forall(|i:usize|
    //         hax_lib::implies(i < result.coefficients.len(), ||
    //                 result.coefficients[i].abs() <= FIELD_MODULUS
    // ))))]
    #[inline(always)]
    pub(crate) fn ntt_multiply(&self, rhs: &Self) -> Self {
        // hax_debug_debug_assert!(lhs
        //     .coefficients
        //     .into_iter()
        //     .all(|coefficient| coefficient >= 0 && coefficient < 4096));

        let mut out = PolynomialRingElement::ZERO();

        for i in 0..VECTORS_IN_RING_ELEMENT {
            out.coefficients[i] = Vector::ntt_multiply(
                &self.coefficients[i],
                &rhs.coefficients[i],
                ZETAS_TIMES_MONTGOMERY_R[64 + 4 * i],
                ZETAS_TIMES_MONTGOMERY_R[64 + 4 * i + 1],
                ZETAS_TIMES_MONTGOMERY_R[64 + 4 * i + 2],
                ZETAS_TIMES_MONTGOMERY_R[64 + 4 * i + 3],
            );
        }

        out
    }
}

const ZETAS_TIMES_MONTGOMERY_R: [FieldElementTimesMontgomeryR; 128] = [
    -1044, -758, -359, -1517, 1493, 1422, 287, 202, -171, 622, 1577, 182, 962, -1202, -1474, 1468,
    573, -1325, 264, 383, -829, 1458, -1602, -130, -681, 1017, 732, 608, -1542, 411, -205, -1571,
    1223, 652, -552, 1015, -1293, 1491, -282, -1544, 516, -8, -320, -666, -1618, -1162, 126, 1469,
    -853, -90, -271, 830, 107, -1421, -247, -951, -398, 961, -1508, -725, 448, -1065, 677, -1275,
    -1103, 430, 555, 843, -1251, 871, 1550, 105, 422, 587, 177, -235, -291, -460, 1574, 1653, -246,
    778, 1159, -147, -777, 1483, -602, 1119, -1590, 644, -872, 349, 418, 329, -156, -75, 817, 1097,
    603, 610, 1322, -1285, -1465, 384, -1215, -136, 1218, -1335, -874, 220, -1187, -1659, -1185,
    -1530, -1278, 794, -1510, -854, -870, 478, -108, -308, 996, 991, 958, -1460, 1522, 1628,
];

/// Represents an intermediate polynomial splitting step in the NTT. All
/// resulting coefficients are in the normal domain since the zetas have been
/// multiplied by MONTGOMERY_R.
#[inline(always)]
pub(crate) fn ntt_at_layer_1<Vector: Operations>(
    zeta_i: &mut usize,
    mut re: PolynomialRingElement<Vector>,
    _layer: usize,
    _initial_coefficient_bound: usize,
) -> PolynomialRingElement<Vector> {
    //*zeta_i += 2;
    for round in 0..16 {
        re.coefficients[round] = Vector::ntt_layer_1_step(
            re.coefficients[round],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 1],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 2],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 3],
        );
        *zeta_i += 4;
    }
    //*zeta_i -= 2;
    re
}

#[inline(always)]
pub(crate) fn ntt_at_layer_2<Vector: Operations>(
    zeta_i: &mut usize,
    mut re: PolynomialRingElement<Vector>,
    _layer: usize,
    _initial_coefficient_bound: usize,
) -> PolynomialRingElement<Vector> {
    for round in 0..16 {
        *zeta_i += 2;
        re.coefficients[round] = Vector::ntt_layer_2_step(
            re.coefficients[round],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 1],
        );
    }
    re
}

#[inline(always)]
pub(crate) fn ntt_layer_int_vec_step<Vector: Operations>(
    mut a: Vector,
    mut b: Vector,
    zeta_r: i16,
) -> (Vector, Vector) {
    let t = Vector::montgomery_multiply_fe_by_fer(b, zeta_r);
    b = Vector::sub(a, &t);
    a = Vector::add(a, &t);
    (a, b)
}

#[inline(always)]
pub(crate) fn ntt_at_layer_3_plus<Vector: Operations>(
    zeta_i: &mut usize,
    mut re: PolynomialRingElement<Vector>,
    layer: usize,
    _initial_coefficient_bound: usize,
) -> PolynomialRingElement<Vector> {
    debug_assert!(layer >= 3);
    let step = 1 << layer;

    for round in 0..(128 >> layer) {
        *zeta_i += 1;

        let offset = round * step * 2;
        let offset_vec = offset / FIELD_ELEMENTS_IN_VECTOR;
        let step_vec = step / FIELD_ELEMENTS_IN_VECTOR;

        for j in offset_vec..offset_vec + step_vec {
            let (x, y) = ntt_layer_int_vec_step(
                re.coefficients[j],
                re.coefficients[j + step_vec],
                ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            );
            re.coefficients[j] = x;
            re.coefficients[j + step_vec] = y;
        }
    }
    re
}

#[inline(always)]
pub(crate) fn ntt_layer_7_int_vec_step<Vector: Operations>(
    mut a: Vector,
    mut b: Vector,
) -> (Vector, Vector) {
    let t = Vector::multiply_by_constant(b, -1600);
    b = Vector::sub(a, &t);
    a = Vector::add(a, &t);
    (a, b)
}

#[inline(always)]
pub(crate) fn ntt_at_layer_7<Vector: Operations>(
    mut re: PolynomialRingElement<Vector>,
) -> PolynomialRingElement<Vector> {
    let step = VECTORS_IN_RING_ELEMENT / 2;
    for j in 0..step {
        let (x, y) = ntt_layer_7_int_vec_step(re.coefficients[j], re.coefficients[j + step]);
        re.coefficients[j] = x;
        re.coefficients[j + step] = y;
    }
    re
}

#[inline(always)]
pub(crate) fn invert_ntt_at_layer_1<Vector: Operations>(
    zeta_i: &mut usize,
    mut re: PolynomialRingElement<Vector>,
    _layer: usize,
) -> PolynomialRingElement<Vector> {
    *zeta_i -= 2;
    for round in 0..16 {
        re.coefficients[round] = Vector::inv_ntt_layer_1_step(
            re.coefficients[round],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i - 1],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i - 2],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i - 3],
        );
        *zeta_i -= 4;
    }
    *zeta_i += 2;
    re
}

#[inline(always)]
pub(crate) fn invert_ntt_at_layer_2<Vector: Operations>(
    zeta_i: &mut usize,
    mut re: PolynomialRingElement<Vector>,
    _layer: usize,
) -> PolynomialRingElement<Vector> {
    for round in 0..16 {
        *zeta_i -= 2;
        re.coefficients[round] = Vector::inv_ntt_layer_2_step(
            re.coefficients[round],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 1],
        );
    }
    re
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_int_vec_step_reduce<Vector: Operations>(
    mut a: Vector,
    mut b: Vector,
    zeta_r: i16,
) -> (Vector, Vector) {
    let a_minus_b = Vector::sub(b, &a);
    a = Vector::barrett_reduce(Vector::add(a, &b));
    b = Vector::montgomery_multiply_fe_by_fer(a_minus_b, zeta_r);
    (a, b)
}

#[inline(always)]
pub(crate) fn invert_ntt_at_layer_3_plus<Vector: Operations>(
    zeta_i: &mut usize,
    mut re: PolynomialRingElement<Vector>,
    layer: usize,
) -> PolynomialRingElement<Vector> {
    let step = 1 << layer;

    for round in 0..(128 >> layer) {
        *zeta_i -= 1;

        let offset = round * step * 2;
        let offset_vec = offset / FIELD_ELEMENTS_IN_VECTOR;
        let step_vec = step / FIELD_ELEMENTS_IN_VECTOR;

        for j in offset_vec..offset_vec + step_vec {
            let (x, y) = inv_ntt_layer_int_vec_step_reduce(
                re.coefficients[j],
                re.coefficients[j + step_vec],
                ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            );
            re.coefficients[j] = x;
            re.coefficients[j + step_vec] = y;
        }
    }
    re
}

// Use the Cooley–Tukey butterfly to compute an in-place NTT representation
/// of a `KyberPolynomialRingElement`.
///
/// This function operates only on those which were produced by binomial
/// sampling, and thus those which have small coefficients. The small
/// coefficients let us skip the first round of Montgomery reductions.
// TODO: Remove or replace with something that works and is useful for the proof.
// #[cfg_attr(hax, hax_lib::requires(
//     hax_lib::forall(|i:usize|
//         hax_lib::implies(i < re.coefficients.len(), || re.coefficients[i].abs() <= 3
// ))))]
// #[cfg_attr(hax, hax_lib::ensures(|result|
//     hax_lib::forall(|i:usize|
//         hax_lib::implies(i < result.coefficients.len(), ||
//             result.coefficients[i].abs() < FIELD_MODULUS
// ))))]
#[inline(always)]
pub(crate) fn ntt_binomially_sampled_ring_element<Vector: Operations>(
    mut re: PolynomialRingElement<Vector>,
) -> PolynomialRingElement<Vector> {
    // Due to the small coefficient bound, we can skip the first round of
    // Montgomery reductions.
    re = ntt_at_layer_7(re);
    let mut zeta_i = 1;
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 6, 3);
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 5, 3);
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 4, 3);
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 3, 3);
    re = ntt_at_layer_2(&mut zeta_i, re, 2, 3);
    re = ntt_at_layer_1(&mut zeta_i, re, 1, 3);

    re.poly_barrett_reduce()
}

/// Use the Cooley–Tukey butterfly to compute an in-place NTT representation
/// of a `KyberPolynomialRingElement`.
///
/// This function operates on the ring element that partly constitutes
/// the ciphertext.
// TODO: Remove or replace with something that works and is useful for the proof.
// #[cfg_attr(hax, hax_lib::requires(
//     hax_lib::forall(|i:usize|
//         hax_lib::implies(i < re.coefficients.len(), || re.coefficients[i].abs() <= 3328
// ))))]
// #[cfg_attr(hax, hax_lib::ensures(|result|
//     hax_lib::forall(|i:usize|
//         hax_lib::implies(i < result.coefficients.len(), ||
//             result.coefficients[i].abs() < FIELD_MODULUS
// ))))]
#[inline(always)]
pub(crate) fn ntt_vector_u<const VECTOR_U_COMPRESSION_FACTOR: usize, Vector: Operations>(
    mut re: PolynomialRingElement<Vector>,
) -> PolynomialRingElement<Vector> {
    hax_debug_assert!(to_i16_array(re)
        .into_iter()
        .all(|coefficient| coefficient.abs() <= 3328));

    let mut zeta_i = 0;

    re = ntt_at_layer_3_plus(&mut zeta_i, re, 7, 3328);
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 6, 3328);
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 5, 3328);
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 4, 3328);
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 3, 3328);
    re = ntt_at_layer_2(&mut zeta_i, re, 2, 3328);
    re = ntt_at_layer_1(&mut zeta_i, re, 1, 3328);

    re.poly_barrett_reduce()
}

/// Use the Gentleman-Sande butterfly to invert, in-place, the NTT representation
/// of a `KyberPolynomialRingElement`. The coefficients of the output
/// ring element are in the Montgomery domain.
#[inline(always)]
pub(crate) fn invert_ntt_montgomery<const K: usize, Vector: Operations>(
    mut re: PolynomialRingElement<Vector>,
) -> PolynomialRingElement<Vector> {
    // We only ever call this function after matrix/vector multiplication
    hax_debug_assert!(to_i16_array(re)
        .into_iter()
        .all(|coefficient| coefficient.abs() < (K as i16) * FIELD_MODULUS));

    let mut zeta_i = super::constants::COEFFICIENTS_IN_RING_ELEMENT / 2;

    re = invert_ntt_at_layer_1(&mut zeta_i, re, 1);
    re = invert_ntt_at_layer_2(&mut zeta_i, re, 2);
    re = invert_ntt_at_layer_3_plus(&mut zeta_i, re, 3);
    re = invert_ntt_at_layer_3_plus(&mut zeta_i, re, 4);
    re = invert_ntt_at_layer_3_plus(&mut zeta_i, re, 5);
    re = invert_ntt_at_layer_3_plus(&mut zeta_i, re, 6);
    re = invert_ntt_at_layer_3_plus(&mut zeta_i, re, 7);

    hax_debug_assert!(
        to_i16_array(re)[0].abs() < 128 * (K as i16) * FIELD_MODULUS
            && to_i16_array(re)[1].abs() < 128 * (K as i16) * FIELD_MODULUS
    );
    hax_debug_assert!(to_i16_array(re)
        .into_iter()
        .enumerate()
        .skip(2)
        .all(|(i, coefficient)| coefficient.abs() < (128 / (1 << i.ilog2())) * FIELD_MODULUS));

    re.poly_barrett_reduce()
}
