use crate::vector::{to_standard_domain, Operations, FIELD_ELEMENTS_IN_VECTOR};

pub(crate) const ZETAS_TIMES_MONTGOMERY_R: [i16; 128] = {
    hax_lib::fstar!("assert_norm (pow2 16 == 65536)");
    [
        -1044, -758, -359, -1517, 1493, 1422, 287, 202, -171, 622, 1577, 182, 962, -1202, -1474,
        1468, 573, -1325, 264, 383, -829, 1458, -1602, -130, -681, 1017, 732, 608, -1542, 411,
        -205, -1571, 1223, 652, -552, 1015, -1293, 1491, -282, -1544, 516, -8, -320, -666, -1618,
        -1162, 126, 1469, -853, -90, -271, 830, 107, -1421, -247, -951, -398, 961, -1508, -725,
        448, -1065, 677, -1275, -1103, 430, 555, 843, -1251, 871, 1550, 105, 422, 587, 177, -235,
        -291, -460, 1574, 1653, -246, 778, 1159, -147, -777, 1483, -602, 1119, -1590, 644, -872,
        349, 418, 329, -156, -75, 817, 1097, 603, 610, 1322, -1285, -1465, 384, -1215, -136, 1218,
        -1335, -874, 220, -1187, -1659, -1185, -1530, -1278, 794, -1510, -854, -870, 478, -108,
        -308, 996, 991, 958, -1460, 1522, 1628,
    ]
};

// A function to retrieve zetas so that we can add a post-condition
#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(i < 128)]
#[hax_lib::ensures(|result| fstar!("Spec.Utils.is_i16b 1664 result"))]
pub fn zeta(i: usize) -> i16 {
    ZETAS_TIMES_MONTGOMERY_R[i]
}

pub(crate) const VECTORS_IN_RING_ELEMENT: usize =
    super::constants::COEFFICIENTS_IN_RING_ELEMENT / FIELD_ELEMENTS_IN_VECTOR;

#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        interface,
        "let to_spec_matrix_t (#r:Spec.MLKEM.rank) (#v_Vector: Type0)
    {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    (m:t_Array (t_Array (t_PolynomialRingElement v_Vector) r) r) : Spec.MLKEM.matrix r =
    createi r (fun i -> to_spec_vector_t #r #v_Vector (m.[i]))"
    )
)]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        interface,
        "let to_spec_vector_t (#r:Spec.MLKEM.rank) (#v_Vector: Type0)
    {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    (m:t_Array (t_PolynomialRingElement v_Vector) r) : Spec.MLKEM.vector r =
    createi r (fun i -> to_spec_poly_t #v_Vector (m.[i]))"
    )
)]
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        interface,
        "let to_spec_poly_t (#v_Vector: Type0)
    {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    (p: t_PolynomialRingElement v_Vector) : Spec.MLKEM.polynomial =
    createi (sz 256) (fun i -> Spec.MLKEM.Math.to_spec_fe 
                                (Seq.index (i2._super_8706949974463268012.f_repr 
                                    (Seq.index p.f_coefficients (v i / 16))) (v i % 16)))"
    )
)]
// XXX: We don't want to copy this. But for eurydice we have to have this.
#[derive(Clone, Copy)]
pub(crate) struct PolynomialRingElement<Vector: Operations> {
    pub(crate) coefficients: [Vector; VECTORS_IN_RING_ELEMENT],
}

#[allow(non_snake_case)]
fn ZERO<Vector: Operations>() -> PolynomialRingElement<Vector> {
    PolynomialRingElement {
        // FIXME:  The THIR body of item DefId(0:415 ~ libcrux_ml_kem[9000]::polynomial::{impl#0}::ZERO::{constant#0}) was stolen.
        coefficients: [Vector::ZERO(); 16],
    }
}

#[inline(always)]
#[hax_lib::requires(VECTORS_IN_RING_ELEMENT * 16 <= a.len())]
fn from_i16_array<Vector: Operations>(a: &[i16]) -> PolynomialRingElement<Vector> {
    let mut result = ZERO();
    for i in 0..VECTORS_IN_RING_ELEMENT {
        result.coefficients[i] = Vector::from_i16_array(&a[i * 16..(i + 1) * 16]);
    }
    result
}

/// Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
/// sum of their constituent coefficients.
#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
fn add_to_ring_element<Vector: Operations, const K: usize>(
    myself: &mut PolynomialRingElement<Vector>,
    rhs: &PolynomialRingElement<Vector>,
) {
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for i in 0..myself.coefficients.len() {
        myself.coefficients[i] = Vector::add(myself.coefficients[i], &rhs.coefficients[i]);
    }
    ()
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
fn poly_barrett_reduce<Vector: Operations>(myself: &mut PolynomialRingElement<Vector>) {
    // Using `hax_lib::fstar::verification_status(lax)` works but produces an error while extracting
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for i in 0..VECTORS_IN_RING_ELEMENT {
        myself.coefficients[i] = Vector::barrett_reduce(myself.coefficients[i]);
    }
    ()
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
fn subtract_reduce<Vector: Operations>(
    myself: &PolynomialRingElement<Vector>,
    mut b: PolynomialRingElement<Vector>,
) -> PolynomialRingElement<Vector> {
    // Using `hax_lib::fstar::verification_status(lax)` works but produces an error while extracting
    for i in 0..VECTORS_IN_RING_ELEMENT {
        let coefficient_normal_form =
            Vector::montgomery_multiply_by_constant(b.coefficients[i], 1441);
        b.coefficients[i] = Vector::barrett_reduce(Vector::sub(
            myself.coefficients[i],
            &coefficient_normal_form,
        ));
    }
    b
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
fn add_message_error_reduce<Vector: Operations>(
    myself: &PolynomialRingElement<Vector>,
    message: &PolynomialRingElement<Vector>,
    mut result: PolynomialRingElement<Vector>,
) -> PolynomialRingElement<Vector> {
    // Using `hax_lib::fstar::verification_status(lax)` works but produces an error while extracting
    for i in 0..VECTORS_IN_RING_ELEMENT {
        let coefficient_normal_form =
            Vector::montgomery_multiply_by_constant(result.coefficients[i], 1441);

        // FIXME: Eurydice crashes with:
        //
        // Warning 11: in top-level declaration libcrux_ml_kem.polynomial.{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}.add_message_error_reduce__libcrux_ml_kem_libcrux_polynomials_PortableVector: this expression is not Low*; the enclosing function cannot be translated into C*: let mutable ret(Mark.Present,(Mark.AtMost 2), ): int16_t[16size_t] = $any in
        // libcrux_ml_kem.libcrux_polynomials.{(libcrux_ml_kem::libcrux_polynomials::libcrux_traits::Operations␣for␣libcrux_ml_kem::libcrux_polynomials::PortableVector)}.add ((@9: libcrux_ml_kem_libcrux_polynomials_PortableVector[16size_t]*)[0uint32_t]:int16_t[16size_t][16size_t])[@4] &(((@8: libcrux_ml_kem_libcrux_polynomials_PortableVector[16size_t]*)[0uint32_t]:libcrux_ml_kem_libcrux_polynomials_PortableVector[16size_t])[@4]) @0;
        // @0
        // Warning 11 is fatal, exiting.
        //
        // On the following code:

        // ```rust
        // result.coefficients[i] = Vector::barrett_reduce(Vector::add(
        //     coefficient_normal_form,
        //     &Vector::add(myself.coefficients[i], &message.coefficients[i]),
        // ));
        // ```

        let tmp = Vector::add(myself.coefficients[i], &message.coefficients[i]);
        let tmp = Vector::add(coefficient_normal_form, &tmp);
        result.coefficients[i] = Vector::barrett_reduce(tmp);
    }
    result
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
fn add_error_reduce<Vector: Operations>(
    myself: &mut PolynomialRingElement<Vector>,
    error: &PolynomialRingElement<Vector>,
) {
    // Using `hax_lib::fstar::verification_status(lax)` works but produces an error while extracting
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for j in 0..VECTORS_IN_RING_ELEMENT {
        let coefficient_normal_form =
            Vector::montgomery_multiply_by_constant(myself.coefficients[j], 1441);

        myself.coefficients[j] =
            Vector::barrett_reduce(Vector::add(coefficient_normal_form, &error.coefficients[j]));
    }
    ()
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
fn add_standard_error_reduce<Vector: Operations>(
    myself: &mut PolynomialRingElement<Vector>,
    error: &PolynomialRingElement<Vector>,
) {
    // Using `hax_lib::fstar::verification_status(lax)` works but produces an error while extracting
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for j in 0..VECTORS_IN_RING_ELEMENT {
        // The coefficients are of the form aR^{-1} mod q, which means
        // calling to_montgomery_domain() on them should return a mod q.
        let coefficient_normal_form = to_standard_domain::<Vector>(myself.coefficients[j]);

        myself.coefficients[j] =
            Vector::barrett_reduce(Vector::add(coefficient_normal_form, &error.coefficients[j]));
    }
    ()
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
#[hax_lib::fstar::verification_status(lax)]
fn ntt_multiply<Vector: Operations>(
    myself: &PolynomialRingElement<Vector>,
    rhs: &PolynomialRingElement<Vector>,
) -> PolynomialRingElement<Vector> {
    let mut out = ZERO();

    for i in 0..VECTORS_IN_RING_ELEMENT {
        out.coefficients[i] = Vector::ntt_multiply(
            &myself.coefficients[i],
            &rhs.coefficients[i],
            zeta(64 + 4 * i),
            zeta(64 + 4 * i + 1),
            zeta(64 + 4 * i + 2),
            zeta(64 + 4 * i + 3),
        );
    }

    out
}

#[hax_lib::attributes]
impl<Vector: Operations> PolynomialRingElement<Vector> {
    #[allow(non_snake_case)]
    pub(crate) fn ZERO() -> Self {
        Self {
            coefficients: [Vector::ZERO(); 16],
        }
    }

    #[inline(always)]
    #[requires(VECTORS_IN_RING_ELEMENT * 16 <= a.len())]
    pub(crate) fn from_i16_array(a: &[i16]) -> Self {
        from_i16_array(a)
    }

    /// Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
    /// sum of their constituent coefficients.
    #[inline(always)]
    pub(crate) fn add_to_ring_element<const K: usize>(&mut self, rhs: &Self) {
        add_to_ring_element::<Vector, K>(self, rhs);
    }

    #[inline(always)]
    pub(crate) fn poly_barrett_reduce(&mut self) {
        poly_barrett_reduce(self);
    }

    #[inline(always)]
    pub(crate) fn subtract_reduce(&self, b: Self) -> Self {
        subtract_reduce(self, b)
    }

    #[inline(always)]
    pub(crate) fn add_message_error_reduce(&self, message: &Self, result: Self) -> Self {
        add_message_error_reduce(self, message, result)
    }

    #[inline(always)]
    pub(crate) fn add_error_reduce(&mut self, error: &Self) {
        add_error_reduce(self, error);
    }

    #[inline(always)]
    pub(crate) fn add_standard_error_reduce(&mut self, error: &Self) {
        add_standard_error_reduce(self, error);
    }

    #[inline(always)]
    pub(crate) fn ntt_multiply(&self, rhs: &Self) -> Self {
        ntt_multiply(self, rhs)
    }
}
