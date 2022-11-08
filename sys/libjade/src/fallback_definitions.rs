#[cfg(not(simd128))]
pub mod simd128;
#[cfg(not(simd128))]
pub use simd128::*;
#[cfg(not(simd256))]
pub mod simd256;
#[cfg(not(simd256))]
pub use simd256::*;
