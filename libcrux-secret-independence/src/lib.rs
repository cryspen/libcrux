mod traits;
pub use traits::*;

mod secret_integers_jan;
pub mod secret_sequences;

/**
* TODO:
* - add array module here
* - add scalar marker trait to traits
* - impl for u* and i*
* - replace old array-like things
*/

#[cfg(all(not(hax), feature = "secret_independence"))]
mod secret_integers;
#[cfg(all(not(hax), feature = "secret_independence"))]
pub use secret_integers::*;

#[cfg(any(hax, not(feature = "secret_independence")))]
mod public_integers;
#[cfg(any(hax, not(feature = "secret_independence")))]
pub use public_integers::*;

#[cfg(test)]
mod tests {
    use super::{
        secret_sequences::{arrayref::SecretArrayRef, slice::SecretSlice},
        traits::{Classify, Declassify},
    };

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
        let secret_slice: SecretSlice<_> = secret_array.as_slice();
        let _: &[u8] = secret_slice.declassify();

        // we can declassify to a full array reference (incl. length)
        let secret_array_ref: SecretArrayRef<_, 9> = secret_array.as_ref();
        let _: &[u8; 9] = secret_array_ref.declassify();

        // we can turn the array ref into a slice and declassify to a slice
        let secret_slice: SecretSlice<_> = secret_array_ref.as_slice();
        let _: &[u8] = secret_slice.declassify();
    }
}
