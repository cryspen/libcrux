extern crate alloc;

/// Indicates an error has occurred
#[derive(Debug)]
pub enum Error {
    /// The used key length is invalid.
    InvalidKeyLength,
    /// The used digest length is invalid.
    InvalidDigestLength,
    ///The maximum input length is exceeded.
    MaximumLengthExceeded,
    /// The maximum chunk length is exceeded.
    InvalidChunkLength,
    /// An unexpected error has occurred.
    Unexpected,
}

impl alloc::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let text = match self {
            Error::InvalidKeyLength => "The used key length is invalid.",
            Error::InvalidDigestLength => "The used digest length is invalid.",
            Error::MaximumLengthExceeded => "The maximum input length is exceeded.",
            Error::InvalidChunkLength => "The maximum chunk length is exceeded.",
            Error::Unexpected => "An unexpected error has occurred.",
        };

        write!(f, "{text}")
    }
}

impl core::error::Error for Error {}
