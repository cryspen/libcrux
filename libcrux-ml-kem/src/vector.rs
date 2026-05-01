//! # Polynomials for libcrux
//!
//! This crate abstracts efficient implementations of polynomials for algorithms
//! such as ML-KEM and ML-DSA.
//!
//! The crate only defines a common API.
//! The actual implementations are in separate crates for different platforms for
//! performance reasons.
//!
//! FIXME: This is kyber specific for now.

pub(crate) mod traits;
pub(crate) use traits::{
    Operations, FIELD_ELEMENTS_IN_VECTOR, FIELD_MODULUS, MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS,
};

// XXX: This is not used on neon right now
#[cfg(feature = "simd256")]
pub(crate) mod rej_sample_table;

// There's no runtime detection here. This either exposes the real SIMD vector,
// or the portable when the feature is not set.
//
// The consumer needs to use runtime feature detection and the appropriate vector
// in each case.
#[cfg(feature = "simd128")]
mod neon;
#[cfg(feature = "simd128")]
pub(crate) use neon::SIMD128Vector;
#[cfg(feature = "simd256")]
mod avx2;
#[cfg(feature = "simd256")]
pub(crate) use avx2::SIMD256Vector;

pub mod portable;

pub(crate) const VECTORS_IN_RING_ELEMENT: usize = 16;

// XXX: We don't want to copy this. But for eurydice we have to have this.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub(crate) struct PolynomialRingElement<Vector: Operations> {
    pub(crate) coefficients: [Vector; VECTORS_IN_RING_ELEMENT],
}

/// Impl→spec lift functions at the polynomial / vector / matrix level.
///
/// These bridge from the impl-side `PolynomialRingElement<Vector>`
/// (a struct holding 16 trait-`Vector`s, each carrying 16 i16 lanes)
/// to the canonical Hacspec spec types
/// (`hacspec_ml_kem::parameters::{Polynomial, Vector, Matrix}`,
/// equivalently `[FieldElement; 256]` / `[Polynomial; RANK]` /
/// `[Vector<RANK>; RANK]`).
///
/// Defined here (NOT in `vector::traits::spec`) because they depend
/// on `PolynomialRingElement` which lives at this layer.  The
/// per-lane / per-array lifts (`i16_to_spec_fe`,
/// `mont_i16_to_spec_fe`, `i16_to_spec_array`,
/// `mont_i16_to_spec_array`) live in `vector::traits::spec` because
/// they're at the vector-of-16-lanes layer.  These polynomial-level
/// lifts compose `i16_to_spec_array` with the trait `to_i16_array`
/// extraction over the 16 chunks.
///
/// One source of truth: the `_t` suffix of the prior F* injection is
/// dropped (no longer F*-only).  These extract to
/// `Libcrux_ml_kem.Vector.Spec.{poly_to_spec, vector_to_spec, matrix_to_spec}`.
#[cfg(hax)]
#[allow(dead_code, unused_variables)]
pub(crate) mod spec {
    use super::PolynomialRingElement;
    use crate::vector::traits::spec::i16_to_spec_array;
    use crate::vector::traits::Operations;
    use hacspec_ml_kem::parameters::{createi, FieldElement};

    /// Lift one impl `PolynomialRingElement<V>` (16 chunks × 16 lanes)
    /// to the spec `[FieldElement; 256]` polynomial.  Each `i16`
    /// coefficient is reduced via `i16_to_spec_fe` (Euclidean mod q).
    pub fn poly_to_spec<V: Operations>(p: &PolynomialRingElement<V>) -> [FieldElement; 256] {
        let flat: [i16; 256] = createi(|i| {
            let chunk = V::to_i16_array(p.coefficients[i / 16]);
            chunk[i % 16]
        });
        i16_to_spec_array(&flat)
    }

    /// Lift a rank-K array of impl polynomials to the spec
    /// `[Polynomial; K]` vector.  Used by libcrux-side ensures that
    /// state per-vector functional correctness against the Hacspec
    /// reference (e.g. `serialize_public_key`).
    pub fn vector_to_spec<const RANK: usize, V: Operations>(
        v: &[PolynomialRingElement<V>; RANK],
    ) -> [[FieldElement; 256]; RANK] {
        createi(|i| poly_to_spec(&v[i]))
    }

    /// Lift a K×K matrix of impl polynomials to the spec
    /// `[[Polynomial; K]; K]` matrix.
    pub fn matrix_to_spec<const RANK: usize, V: Operations>(
        m: &[[PolynomialRingElement<V>; RANK]; RANK],
    ) -> [[[FieldElement; 256]; RANK]; RANK] {
        createi(|i| vector_to_spec(&m[i]))
    }
}
