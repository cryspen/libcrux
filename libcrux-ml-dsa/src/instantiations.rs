// TODO

// macro_rules! instantiate {
//     ($modp:ident, $vector:path, $hash:path) => {
//         pub mod $modp {}
//     };
// }

// // Portable generic implementations.
// instantiate! {portable, crate::simd::portable::PortableSIMDUnit, crate::hash_functions::portable::PortableHash<K>}

// // AVX2 generic implementation.
// // #[cfg(feature = "simd256")]
// instantiate! {avx2, crate::simd::avx2::AVX2SIMDUnit, crate::hash_functions::avx2::Simd256Hash}

// // NEON generic implementation.
// #[cfg(feature = "simd128")]
// instantiate! {neon, crate::vector::SIMD128Vector, crate::hash_functions::neon::Simd128Hash}
