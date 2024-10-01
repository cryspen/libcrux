pub(crate) const FIELD_MODULUS: i32 = 8_380_417;

pub(crate) const COEFFICIENTS_IN_RING_ELEMENT: usize = 256;

pub(crate) const FIELD_MODULUS_MINUS_ONE_BIT_LENGTH: usize = 23;

pub(crate) const BITS_IN_LOWER_PART_OF_T: usize = 13;
pub(crate) const RING_ELEMENT_OF_T0S_SIZE: usize =
    (BITS_IN_LOWER_PART_OF_T * COEFFICIENTS_IN_RING_ELEMENT) / 8;

pub(crate) const BITS_IN_UPPER_PART_OF_T: usize =
    FIELD_MODULUS_MINUS_ONE_BIT_LENGTH - BITS_IN_LOWER_PART_OF_T;
pub(crate) const RING_ELEMENT_OF_T1S_SIZE: usize =
    (BITS_IN_UPPER_PART_OF_T * COEFFICIENTS_IN_RING_ELEMENT) / 8;

pub(crate) const SEED_FOR_A_SIZE: usize = 32;
pub(crate) const SEED_FOR_ERROR_VECTORS_SIZE: usize = 64;
pub(crate) const BYTES_FOR_VERIFICATION_KEY_HASH: usize = 64;
pub(crate) const SEED_FOR_SIGNING_SIZE: usize = 32;

/// Number of bytes of entropy required for key generation.
pub const KEY_GENERATION_RANDOMNESS_SIZE: usize = 32;
/// Number of bytes of entropy required for signing.
pub const SIGNING_RANDOMNESS_SIZE: usize = 32;

pub(crate) const MESSAGE_REPRESENTATIVE_SIZE: usize = 64;
pub(crate) const MASK_SEED_SIZE: usize = 64;

pub(crate) const REJECTION_SAMPLE_BOUND_SIGN: usize = 814;

/// The length of `context` is serialized to a single `u8`.
pub(crate) const CONTEXT_MAX_LEN: usize = 255;
