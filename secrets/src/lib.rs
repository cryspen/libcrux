/// Traits are only used internally really.
/// But some of them are bounds on public types for now.
/// Don't try to use the traits outside of this crate though.
mod traits;
pub use traits::*;

// Generally useful modules.
pub mod array;
pub mod util;
pub mod zeroize;

/// The secret variants
///
/// These are more costly for now and MUST NOT be used in regular builds.
#[cfg(not(feature = "public"))]
mod secret {
    mod sequences;
    pub use sequences::*;

    mod integers;
    pub use integers::*;
}
#[cfg(not(feature = "public"))]
pub use secret::*;

/// The public versions
///
/// Enabled with the `public` feature.
#[cfg(feature = "public")]
mod public {
    mod sequences;
    pub use sequences::*;

    mod integers;
    pub use integers::*;
}
#[cfg(feature = "public")]
pub use public::*;

#[cfg(test)]
mod tests {
    use super::traits::{Classify, Declassify};

    #[test]
    fn scalar_example() {
        const MASK: u64 = 0x55aa55aa55aa55aa;
        let secret_answer = 42u64.classify();
        let secret_mask = MASK.classify();

        // we can add a normal value to a secret value
        let masked_secret_answer = secret_answer + MASK;
        assert_eq!(masked_secret_answer.declassify(), 42 + MASK);

        // we can add a secret value to a secret value
        let masked_secret_answer = secret_answer + secret_mask;
        assert_eq!(masked_secret_answer.declassify(), 42 + MASK);
    }

    #[test]
    fn array_examples() {
        let secret_array = b"squeamish".classify();

        // we can turn the array into a slice and declassify to a slice
        let secret_slice = secret_array.as_slice();
        let _declassified_slice = secret_slice.declassify();

        // we can declassify to a full array reference (incl. length)
        let secret_array_ref = secret_array.as_ref();
        let _declassified_ref = secret_array_ref.declassify();

        // we can turn the array ref into a slice and declassify to a slice
        let secret_slice = secret_array_ref.as_slice();
        let _declassified_slice = secret_slice.declassify();
    }
}
