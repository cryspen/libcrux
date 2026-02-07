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
#[cfg_attr(
    hax,
    hax_lib::fstar::after(
        interface,
        r#"let to_spec_poly_t (#v_Vector: Type0)
    {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    (p: t_PolynomialRingElement v_Vector) : Spec.MLKEM.polynomial =
    createi (sz 256) (fun i -> Spec.MLKEM.Math.to_spec_fe 
                                (Seq.index (i2._super_i2.f_repr 
                                    (Seq.index p.f_coefficients (v i / 16))) (v i % 16)))
let to_spec_vector_t (#r:Spec.MLKEM.rank) (#v_Vector: Type0)
    {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    (m:t_Array (t_PolynomialRingElement v_Vector) r) : Spec.MLKEM.vector r =
    createi r (fun i -> to_spec_poly_t #v_Vector (m.[i]))
let to_spec_matrix_t (#r:Spec.MLKEM.rank) (#v_Vector: Type0)
    {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    (m:t_Array (t_Array (t_PolynomialRingElement v_Vector) r) r) : Spec.MLKEM.matrix r =
    createi r (fun i -> to_spec_vector_t #r #v_Vector (m.[i]))"#
    )
)]
#[derive(Clone, Copy)]
#[repr(transparent)]
pub(crate) struct PolynomialRingElement<Vector: Operations> {
    pub(crate) coefficients: [Vector; VECTORS_IN_RING_ELEMENT],
}
