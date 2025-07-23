extern crate alloc;

mod blake2b;
mod blake2s;
mod error;

pub use blake2b::{Blake2b, Blake2bBuilder};
pub use blake2s::{Blake2s, Blake2sBuilder};
pub use error::Error;

/// Type that holds the constants in case both key length and digest length are known at compile
/// time.
pub struct ConstKeyLenConstDigestLen<const KEY_LEN: usize, const OUT_LEN: usize>;

/// Type that holds the constant in case just the key length is known at compile time.
pub struct ConstKeyLen<const KEY_LEN: usize>;

/// Type that holds the constant in case just the digest length is known at compile time.
pub struct ConstDigestLen<const OUT_LEN: usize>;

/// Type that holds the constant in case neither the key length nor the digest length is known at
/// compile time.
pub struct Dynamic;
