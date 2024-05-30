pub(crate) const FIELD_MODULUS: i32 = 8_380_417;

pub(crate) const COEFFICIENTS_IN_RING_ELEMENT: usize = 256;

pub(crate) const FIELD_MODULUS_MINUS_ONE_BIT_LENGTH: usize = 23;

pub(crate) const BITS_IN_LOWER_PART_OF_T: usize = 13;

pub(crate) const BITS_IN_UPPER_PART_OF_T: usize =
    FIELD_MODULUS_MINUS_ONE_BIT_LENGTH - BITS_IN_LOWER_PART_OF_T;
pub(crate) const BYTES_IN_RING_ELEMENT_OF_T1S: usize =
    (BITS_IN_UPPER_PART_OF_T * COEFFICIENTS_IN_RING_ELEMENT) / 8;

pub(crate) const SEED_FOR_A_SIZE: usize = 32;
pub(crate) const SEED_FOR_ERROR_VECTORS_SIZE: usize = 64;
pub(crate) const HASH_OF_PUBLIC_KEY_SIZE: usize = 64;
pub(crate) const SEED_FOR_SIGNING_SIZE: usize = 32;
