use crate::Error;

/// An RSA Signature that is `LEN` bytes long.
#[derive(Debug)]
pub struct Signature<const LEN: usize>([u8; LEN]);

/// An RSA Public Key that is `LEN` bytes long.
#[derive(Debug, Clone)]
pub struct PublicKey<const LEN: usize> {
    n: [u8; LEN],
}

impl<const LEN: usize> From<[u8; LEN]> for PublicKey<LEN> {
    fn from(n: [u8; LEN]) -> Self {
        Self { n }
    }
}

/// An RSA Private Key that is `LEN` bytes long.
pub struct PrivateKey<const LEN: usize> {
    pk: PublicKey<LEN>,
    d: [u8; LEN],
}

impl<const LEN: usize> PrivateKey<LEN> {
    /// Constructor for the private key based on `n` and `d`.
    pub fn from_components(n: [u8; LEN], d: [u8; LEN]) -> Self {
        Self { pk: n.into(), d }
    }

    /// Returns the public key of the private key.
    pub fn pk(&self) -> &PublicKey<LEN> {
        &self.pk
    }
}

const E_BITS: u32 = 17;
const E: [u8; 3] = [1, 0, 1];

fn hacl_hash_alg(alg: crate::DigestAlgorithm) -> libcrux_hacl_rs::streaming_types::hash_alg {
    match alg {
        crate::DigestAlgorithm::Sha2_256 => libcrux_hacl_rs::streaming_types::hash_alg::SHA2_256,
        crate::DigestAlgorithm::Sha2_384 => libcrux_hacl_rs::streaming_types::hash_alg::SHA2_384,
        crate::DigestAlgorithm::Sha2_512 => libcrux_hacl_rs::streaming_types::hash_alg::SHA2_512,
    }
}

// next up: generate these in macros

macro_rules! impl_rsapss {
    ($sign_fn:ident, $verify_fn:ident, $bits:literal, $bytes:literal) => {
        /// Computes a signature over `msg` using `sk` and writes it to `sig`.
        /// Returns `Ok(())` on success.
        ///
        /// Returns an error in any of the following cases:
        /// - the secret key is invalid
        /// - the length of `msg` exceeds `u32::MAX`
        /// - `salt_len` exceeds `u32::MAX - alg.hash_len() - 8`
        ///
        /// Ensures that the preconditions to hacl functions hold:
        ///
        /// - `sLen + Hash.hash_length a + 8 <= max_size_t`
        ///   - checked explicitly
        /// - `(sLen + Hash.hash_length a + 8) less_than_max_input_length a`
        ///   - `max_input_length` is at least `2^62 - 1`, can't be reached since everyting
        ///     is less than `u32::MAX`.
        /// - `sLen + Hash.hash_length a + 2 <= blocks (modBits - 1) 8`
        ///   - `blocks a b = (a - 1) / b + 1`, i.e. `ceil(div(a, b))`
        ///   - checked explicitly
        /// - `msgLen `less_than_max_input_length` a`
        ///   - follows from the check that messages are shorter than `u32::MAX`.
        pub fn $sign_fn(
            alg: crate::DigestAlgorithm,
            sk: &PrivateKey<$bytes>,
            msg: &[u8],
            salt: &[u8],
            sig: &mut Signature<$bytes>,
        ) -> Result<(), Error> {
            let salt_len = salt.len().try_into().map_err(|_| Error::SaltTooLarge)?;
            let msg_len = msg.len().try_into().map_err(|_| Error::MessageTooLarge)?;

            // required by precondition to verify, see
            // https://github.com/hacl-star/hacl-star/blob/efbf82f29190e2aecdac8899e4f42c8cb9defc98/code/rsapss/Hacl.Spec.RSAPSS.fst#L162
            // all operands are at most u32, so coercing to u64 and then adding is safe.
            if (salt_len as u64) + alg.hash_len() as u64 + 8 > u32::MAX as u64 {
                return Err(Error::SaltTooLarge);
            }

            let a = hacl_hash_alg(alg);
            let mod_bits = $bits;
            let e_bits = E_BITS;
            let d_bits = $bits;
            let sgnt = &mut sig.0;

            // required by precondition to verify, see
            // https://github.com/hacl-star/hacl-star/blob/efbf82f29190e2aecdac8899e4f42c8cb9defc98/code/rsapss/Hacl.Spec.RSAPSS.fst#L164
            // all operands are at most u32, so coercing to u64 and then adding is safe.
            if salt_len as u64 + alg.hash_len() as u64 + 2 > (mod_bits as u64 - 1) / 8 + 1 {
                return Err(Error::SaltTooLarge);
            }

            match crate::hacl::rsapss::rsapss_skey_sign(
                a, mod_bits, e_bits, d_bits, &sk.pk.n, &E, &sk.d, salt_len, salt, msg_len, msg,
                sgnt,
            ) {
                true => Ok(()),
                false => Err(Error::SigningFailed),
            }
        }

        /// Returns `Ok(())` if the provided signature is valid.
        ///
        /// Returns an error in any of the following cases:
        /// - the public key is invalid
        /// - the signature verification fails
        /// - the length of `msg` exceeds `u32::MAX`
        /// - `salt_len` exceeds `u32::MAX - alg.hash_len() - 8`
        ///
        /// Ensures that the preconditions to hacl functions hold:
        ///
        /// - `sLen + Hash.hash_length a + 8 <= max_size_t`
        ///   - checked explicitly
        /// - `(sLen + Hash.hash_length a + 8) less_than_max_input_length a`
        ///   - `max_input_length` is at least `2^62 - 1`, can't be reached since everyting
        ///     is less than `u32::MAX`.
        /// - `msgLen less_than_max_input_length a`
        ///   - follows from the check that messages are shorter than `u32::MAX`.
        pub fn $verify_fn(
            alg: crate::DigestAlgorithm,
            pk: &PublicKey<$bytes>,
            msg: &[u8],
            salt_len: u32,
            sig: &Signature<$bytes>,
        ) -> Result<(), Error> {
            // required by precondition to verify, see
            // https://github.com/hacl-star/hacl-star/blob/efbf82f29190e2aecdac8899e4f42c8cb9defc98/code/rsapss/Hacl.Spec.RSAPSS.fst#L236
            // all operands are at most u32, so coercing to u64 and then adding is safe.
            if (salt_len as u64) + alg.hash_len() as u64 + 8 > u32::MAX as u64 {
                return Err(Error::SaltTooLarge);
            }

            let msg_len = msg.len().try_into().map_err(|_| Error::MessageTooLarge)?;

            let a = hacl_hash_alg(alg);
            let mod_bits = $bits;
            let e_bits = E_BITS;
            let sgnt = &sig.0;

            match crate::hacl::rsapss::rsapss_pkey_verify(
                a, mod_bits, e_bits, &pk.n, &E, salt_len, $bytes, /*signature length*/
                sgnt, msg_len, msg,
            ) {
                true => Ok(()),
                false => Err(Error::VerificationFailed),
            }
        }
    };
}

impl_rsapss!(sign_2048, verify_2048, 2048, 256);
impl_rsapss!(sign_3072, verify_3072, 3072, 384);
impl_rsapss!(sign_4096, verify_4096, 4096, 512);
impl_rsapss!(sign_6144, verify_6144, 6144, 768);
impl_rsapss!(sign_8192, verify_8192, 8192, 1024);

#[cfg(test)]
mod tests {
    use super::*;

    const MODULUS: [u8; 256] = [
        0xd2, 0x78, 0x16, 0xcb, 0x72, 0xbb, 0x6e, 0x27, 0xdb, 0x10, 0x1a, 0x6f, 0x3e, 0x64, 0x62,
        0x93, 0xd9, 0xec, 0xa7, 0xb3, 0x98, 0xe3, 0x36, 0x6c, 0x9e, 0x69, 0x31, 0xc4, 0x5d, 0xd7,
        0x24, 0xd3, 0xf8, 0x90, 0xb0, 0xd0, 0x57, 0x78, 0x3e, 0xdd, 0xee, 0xf0, 0xc9, 0x0e, 0x98,
        0x6d, 0xad, 0xe9, 0x46, 0x47, 0xc5, 0xcb, 0x4d, 0xa4, 0xc6, 0x9c, 0x83, 0x1a, 0x13, 0x9f,
        0xb7, 0x8d, 0xe7, 0xe3, 0x79, 0x97, 0xf2, 0x9e, 0x36, 0x5c, 0x96, 0xaa, 0xf6, 0x29, 0xfe,
        0x6e, 0x3c, 0x0d, 0xb0, 0xcb, 0x04, 0x7d, 0x35, 0xd3, 0xeb, 0xf7, 0xee, 0x36, 0x59, 0xda,
        0xb5, 0xb2, 0x34, 0x08, 0x86, 0x87, 0x27, 0x02, 0x4b, 0x49, 0xb3, 0x85, 0x33, 0x9b, 0x63,
        0x8f, 0x28, 0x3b, 0x27, 0x83, 0x65, 0xf9, 0x62, 0x23, 0xe0, 0x8b, 0x15, 0x1d, 0xd3, 0x00,
        0xb1, 0xd6, 0x37, 0x3e, 0x7b, 0xa7, 0x1d, 0xc7, 0x63, 0x79, 0xe2, 0xa2, 0xca, 0x2d, 0xa4,
        0xb6, 0xcd, 0xef, 0x8d, 0x73, 0xec, 0x56, 0xfc, 0x0b, 0xac, 0xcb, 0x80, 0x53, 0xcf, 0x34,
        0x2f, 0x29, 0xb0, 0xe7, 0xf0, 0xb9, 0x24, 0xf4, 0xe4, 0x99, 0xb2, 0x58, 0xc0, 0x9e, 0x1f,
        0xf5, 0x43, 0x6e, 0xca, 0xc6, 0xeb, 0x65, 0xd0, 0x5f, 0xdb, 0x13, 0x4c, 0x8c, 0xca, 0x82,
        0xd9, 0xad, 0xc1, 0xfd, 0x7a, 0xd9, 0x78, 0xc7, 0xed, 0xdf, 0xc9, 0x70, 0x54, 0xd3, 0x80,
        0x5f, 0x06, 0x48, 0x11, 0x6e, 0xfb, 0x9b, 0x46, 0xfa, 0x02, 0x65, 0xde, 0xcc, 0xe9, 0x6e,
        0x91, 0x98, 0x93, 0x3d, 0x3d, 0x6d, 0xb1, 0x99, 0xa4, 0x73, 0xc1, 0x2c, 0xa2, 0x16, 0x55,
        0x97, 0xf3, 0x0f, 0x67, 0xf7, 0x9a, 0x78, 0x74, 0x15, 0x66, 0xb1, 0xd4, 0xdc, 0x98, 0x47,
        0x8a, 0x50, 0xb6, 0x2d, 0x63, 0xf9, 0xce, 0xa2, 0x76, 0x70, 0x91, 0xa8, 0x3b, 0x00, 0x28,
        0x01,
    ];

    const PRIVATE_EXPONENT: [u8; 256] = [
        0x5a, 0x90, 0x21, 0xfe, 0xd9, 0x17, 0x9d, 0x86, 0xb8, 0xd4, 0x6d, 0x0b, 0x81, 0x25, 0x60,
        0xe5, 0x8d, 0xd8, 0x2f, 0x31, 0x30, 0x90, 0x54, 0x52, 0xd8, 0xb7, 0x1b, 0x1b, 0x0b, 0xe6,
        0x0f, 0x8a, 0xc6, 0x62, 0x3c, 0x32, 0xe9, 0xf0, 0x6b, 0xdc, 0xc3, 0x7c, 0x08, 0x87, 0xa7,
        0x3f, 0x4a, 0x9e, 0x1e, 0x07, 0xb4, 0x2c, 0x8e, 0xf4, 0x60, 0x21, 0xe8, 0xa7, 0xc7, 0xd9,
        0xe9, 0xf9, 0xbd, 0xd6, 0x3b, 0xf4, 0x0e, 0x09, 0xd6, 0x0a, 0x71, 0x2a, 0x8f, 0x51, 0xf2,
        0x91, 0x2c, 0x76, 0x17, 0xa4, 0xc4, 0x01, 0xbc, 0xaf, 0xbb, 0xd1, 0xab, 0x46, 0xe7, 0xd3,
        0x1c, 0x6b, 0xd9, 0xc7, 0xf1, 0x5b, 0x26, 0x85, 0xee, 0x2f, 0x80, 0x77, 0xc8, 0x85, 0x0c,
        0x8a, 0x05, 0x1d, 0xaf, 0x1a, 0xf3, 0x3e, 0x23, 0xe4, 0x9c, 0x32, 0x3c, 0x9b, 0xe0, 0xb7,
        0x63, 0xce, 0x71, 0x67, 0x09, 0x7e, 0x17, 0x69, 0x74, 0x9a, 0xec, 0x2a, 0x71, 0xf4, 0xeb,
        0xe2, 0x84, 0x23, 0x8b, 0xa8, 0x27, 0x69, 0x19, 0x53, 0x52, 0x8f, 0xc3, 0x62, 0xd5, 0x2a,
        0x43, 0xb0, 0x78, 0x90, 0x54, 0x98, 0x22, 0x12, 0x2d, 0x32, 0x28, 0xcf, 0xf9, 0x04, 0x1c,
        0x4f, 0x28, 0xb7, 0xad, 0x98, 0x1a, 0xdf, 0x2e, 0xdb, 0x94, 0xd5, 0x3d, 0xe2, 0xa9, 0x29,
        0x3c, 0x3e, 0xaa, 0x81, 0x2a, 0x61, 0x8d, 0x4b, 0x41, 0x2f, 0xda, 0x99, 0x8b, 0x78, 0x7a,
        0xd5, 0xec, 0x93, 0x53, 0x5a, 0x84, 0x43, 0x47, 0x1a, 0xaf, 0x68, 0xa7, 0x5f, 0x4e, 0x62,
        0xe5, 0xcf, 0x07, 0xc9, 0x2b, 0x67, 0x34, 0x82, 0x27, 0xf6, 0xe0, 0x6d, 0x51, 0xca, 0x21,
        0xea, 0xfa, 0x32, 0xf0, 0x9f, 0x84, 0xb4, 0xfb, 0xaf, 0x25, 0x1e, 0x91, 0x08, 0x94, 0x5e,
        0x83, 0x7f, 0x0f, 0x6a, 0x86, 0x98, 0x77, 0xb8, 0xb0, 0xca, 0xd0, 0x34, 0x10, 0x69, 0x59,
        0x21,
    ];

    #[test]
    fn self_test_rsa_pss() {
        let pk = PublicKey { n: MODULUS };
        let sk = PrivateKey {
            pk: pk.clone(),
            d: PRIVATE_EXPONENT,
        };
        let salt = [1, 2, 3, 4, 5];
        let msg = [7, 8, 9, 10];
        let mut signature = Signature([0u8; 256]);
        sign_2048(
            crate::DigestAlgorithm::Sha2_256,
            &sk,
            &msg,
            &salt,
            &mut signature,
        )
        .unwrap();
        verify_2048(
            crate::DigestAlgorithm::Sha2_256,
            &pk,
            &msg,
            salt.len() as u32,
            &signature,
        )
        .expect("Error verifying signature");
    }
}
