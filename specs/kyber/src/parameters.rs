pub(crate) const FIELD_MODULUS: u16 = 3329;
pub(crate) const BITS_PER_COEFFICIENT: usize = 12; // floor(log_2(FIELD_MODULUS)) + 1
pub(crate) const COEFFICIENTS_IN_RING_ELEMENT: usize = 256;
pub(crate) const BITS_PER_RING_ELEMENT: usize = COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT;

pub(crate) const BINOMIAL_SAMPLING_COINS: usize = 2;
pub(crate) const REJECTION_SAMPLING_SEED_SIZE: usize = COEFFICIENTS_IN_RING_ELEMENT * 3 * 3;

pub(crate) const RANK: usize = 3;

pub(crate) const CPA_PKE_KEY_GENERATION_SEED_SIZE: usize = 32;

pub(crate) const T_AS_NTT_ENCODED_SIZE : usize = (RANK * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8; //1152
pub(crate) const CPA_PKE_PUBLIC_KEY_SIZE: usize = T_AS_NTT_ENCODED_SIZE + 32; //1184 

pub(crate) const CPA_PKE_SECRET_KEY_SIZE: usize = (RANK * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8; //1152

pub(crate) const U_COMPRESSION_FACTOR : usize = 10;
pub(crate) const V_COMPRESSION_FACTOR : usize = 4;

pub(crate) const U_VECTOR_SIZE : usize = (RANK * COEFFICIENTS_IN_RING_ELEMENT * U_COMPRESSION_FACTOR) / 8;
pub(crate) const V_VECTOR_SIZE : usize = (COEFFICIENTS_IN_RING_ELEMENT * V_COMPRESSION_FACTOR) / 8;

pub(crate) const CPA_PKE_CIPHERTEXT_SIZE : usize = U_VECTOR_SIZE +  V_VECTOR_SIZE;

pub(crate) mod hash_functions {
    macro_rules! G {
        ($input_name: ident) => {
            libcrux::digest::sha3_512($input_name)
        };
    }
    macro_rules! H {
        ($input_name: ident) => {
            libcrux::digest::sha3_256(&$input_name)
        };
    }

    macro_rules! PRF {
        ($output_bytes: literal, $input_name: ident) => {
            libcrux::digest::shake256::<$output_bytes>(&$input_name)
        };
    }
    macro_rules! XOF {
        ($output_bytes: literal, $input_name: ident) => {
            libcrux::digest::shake128::<$output_bytes>(&$input_name)
        };
    }
    macro_rules! KDF {
        ($output_bytes: literal, $input_name: ident) => {
            libcrux::digest::shake256::<$output_bytes>(&$input_name)
        };
    }

    pub(crate) use G;

    pub(crate) use H;
    pub(crate) const H_DIGEST_SIZE: usize =
        libcrux::digest::digest_size(libcrux::digest::Algorithm::Sha3_256);

    pub(crate) use PRF;
    pub(crate) use XOF;
    pub(crate) use KDF;
}
