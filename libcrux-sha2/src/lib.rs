/// The length of a SHA224 hash in bytes.
pub const SHA224_LENGTH: usize = 28;

/// The length of a SHA256 hash in bytes.
pub const SHA256_LENGTH: usize = 32;

/// The length of a SHA384 hash in bytes.
pub const SHA384_LENGTH: usize = 48;

/// The length of a SHA512 hash in bytes.
pub const SHA512_LENGTH: usize = 64;

/// The generated hacl code
#[cfg(feature = "hacl")]
pub mod hacl;

/// The implementation of our types using that hacl code
#[cfg(feature = "hacl")]
mod impl_hacl;

/// use it if we want to use hacl
#[cfg(feature = "portable_hacl")]
pub use impl_hacl::*;
