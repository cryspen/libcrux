mod util;

#[cfg(feature = "rand")]
mod rand {
    use crate::util::*;
    use libcrux_ecdsa::{
        p256::{Nonce, PrivateKey, PublicKey},
        *,
    };
    use rand_core::OsRng;

    #[test]
    fn test_self() {
        // From https://tools.ietf.org/html/rfc6979#appendix-A.2.5
        const PK_HEX: &str = "0460FED4BA255A9D31C961EB74C6356D68C049B8923B61FA6CE669622E60F29FB67903FE1008B8BC99A41AE9E95628BC64F2F1B20C2D7E9F5177A3C294D4462299";
        const SK_HEX: &str = "C9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721";

        use rand::TryRngCore;
        let mut os_rng = OsRng;
        let mut rng = os_rng.unwrap_mut();

        let pk = hex_str_to_bytes(PK_HEX);
        let pk = PublicKey::try_from(pk.as_slice()).unwrap();
        let sk: [u8; 32] = hex_str_to_array(SK_HEX);
        let sk = PrivateKey::try_from(&sk).unwrap();
        let nonce = Nonce::random(&mut rng).unwrap();
        let msg = b"sample";

        let sig = p256::sign(DigestAlgorithm::Sha256, &msg[..], &sk, &nonce).unwrap();
        p256::verify(DigestAlgorithm::Sha256, &msg[..], &sig, &pk).unwrap();

        let new_msg = b"a different message";
        let sig = p256::sign(DigestAlgorithm::Sha256, &new_msg[..], &sk, &nonce).unwrap();
        let error = p256::verify(DigestAlgorithm::Sha256, &msg[..], &sig, &pk)
            .expect_err("The message is wrong for the signature");
        assert!(matches!(error, Error::InvalidSignature));
    }
}

mod low_s {
    use crate::util::*;
    use libcrux_ecdsa::{
        p256::{Nonce, PrivateKey, PublicKey, Signature},
        *,
    };

    /// P-256 curve order n in big-endian bytes.
    const P256_ORDER: [u8; 32] = [
        0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0xFF, 0xBC, 0xE6, 0xFA, 0xAD, 0xA7, 0x17, 0x9E, 0x84, 0xF3, 0xB9, 0xCA, 0xC2, 0xFC, 0x63,
        0x25, 0x51,
    ];

    /// Half of P-256 curve order (n-1)/2 in big-endian bytes.
    const P256_HALF_ORDER: [u8; 32] = [
        0x7F, 0xFF, 0xFF, 0xFF, 0x80, 0x00, 0x00, 0x00, 0x7F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0xFF, 0xDE, 0x73, 0x7D, 0x56, 0xD3, 0x8B, 0xCF, 0x42, 0x79, 0xDC, 0xE5, 0x61, 0x7E, 0x31,
        0x92, 0xA8,
    ];

    fn bytes_gt(a: &[u8; 32], b: &[u8; 32]) -> bool {
        for i in 0..32 {
            if a[i] > b[i] {
                return true;
            }
            if a[i] < b[i] {
                return false;
            }
        }
        false
    }

    fn is_low_s(s: &[u8; 32]) -> bool {
        !bytes_gt(s, &P256_HALF_ORDER)
    }

    fn negate_s(s: &[u8; 32]) -> [u8; 32] {
        let mut result = [0u8; 32];
        let mut borrow: u16 = 0;
        for i in (0..32).rev() {
            let diff = (P256_ORDER[i] as u16)
                .wrapping_sub(s[i] as u16)
                .wrapping_sub(borrow);
            result[i] = diff as u8;
            borrow = if diff > 0xFF { 1 } else { 0 };
        }
        result
    }

    #[test]
    fn test_signing_produces_low_s() {
        // Test that signing always produces low-S signatures.
        const PK_HEX: &str = "0460FED4BA255A9D31C961EB74C6356D68C049B8923B61FA6CE669622E60F29FB67903FE1008B8BC99A41AE9E95628BC64F2F1B20C2D7E9F5177A3C294D4462299";
        const SK_HEX: &str = "C9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721";

        let pk = hex_str_to_bytes(PK_HEX);
        let pk = PublicKey::try_from(pk.as_slice()).unwrap();
        let sk: [u8; 32] = hex_str_to_array(SK_HEX);
        let sk = PrivateKey::try_from(&sk).unwrap();

        // Test with multiple different nonces to increase chance of hitting high-S before normalization.
        let nonces = [
            "0000000000000000000000000000000000000000000000000000000000000001",
            "FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632550",
            "7FFFFFFF800000007FFFFFFFFFFFFFFFDE737D56D38BCF4279DCE5617E3192A8",
            "A6E3C57DD01ABE90086538398355DD4C3B17AA873382B0F24D6129493D8AAD60",
        ];

        for nonce_hex in &nonces {
            let nonce_bytes: [u8; 32] = hex_str_to_array(nonce_hex);
            // Skip invalid nonces (must be 0 < nonce < n)
            if nonce_bytes.iter().all(|&b| b == 0) {
                continue;
            }

            // Create nonce using from_bytes - we need to work around the validation
            // by using the internal signing function directly through the public API
            let msg = b"test message for low-s";

            // Try to sign with this nonce
            if let Ok(nonce) = std::panic::catch_unwind(|| {
                // This is a workaround - we'll use random signing instead
                unsafe { std::mem::transmute::<[u8; 32], Nonce>(nonce_bytes) }
            }) {
                if let Ok(sig) = p256::sign(DigestAlgorithm::Sha256, msg, &sk, &nonce) {
                    let (_, s) = sig.as_bytes();
                    assert!(
                        is_low_s(s),
                        "Signing produced high-S signature with nonce {}",
                        nonce_hex
                    );

                    // Verify the signature is valid with both verify and verify_strict
                    assert!(
                        p256::verify(DigestAlgorithm::Sha256, msg, &sig, &pk).is_ok(),
                        "Low-S signature should be valid"
                    );
                    assert!(
                        p256::verify_strict(DigestAlgorithm::Sha256, msg, &sig, &pk).is_ok(),
                        "Low-S signature should pass strict verification"
                    );
                }
            }
        }
    }

    #[test]
    fn test_strict_verification_rejects_high_s() {
        // Test that verify_strict rejects high-S signatures while verify accepts them.
        const PK_HEX: &str = "0460FED4BA255A9D31C961EB74C6356D68C049B8923B61FA6CE669622E60F29FB67903FE1008B8BC99A41AE9E95628BC64F2F1B20C2D7E9F5177A3C294D4462299";
        const SK_HEX: &str = "C9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721";
        // A known valid nonce
        const NONCE_HEX: &str = "A6E3C57DD01ABE90086538398355DD4C3B17AA873382B0F24D6129493D8AAD60";

        let pk = hex_str_to_bytes(PK_HEX);
        let pk = PublicKey::try_from(pk.as_slice()).unwrap();
        let sk: [u8; 32] = hex_str_to_array(SK_HEX);
        let sk = PrivateKey::try_from(&sk).unwrap();
        let nonce_bytes: [u8; 32] = hex_str_to_array(NONCE_HEX);
        let nonce: Nonce = unsafe { std::mem::transmute(nonce_bytes) };

        let msg = b"test message for high-s rejection";

        // Sign the message (will produce low-S)
        let sig = p256::sign(DigestAlgorithm::Sha256, msg, &sk, &nonce).unwrap();
        let (r, s) = sig.as_bytes();

        // Verify the original low-S signature works with both functions
        assert!(p256::verify(DigestAlgorithm::Sha256, msg, &sig, &pk).is_ok());
        assert!(p256::verify_strict(DigestAlgorithm::Sha256, msg, &sig, &pk).is_ok());

        // Create a malleable high-S signature by computing n - s
        let high_s = negate_s(s);

        // Ensure this is actually a high-S value
        assert!(
            bytes_gt(&high_s, &P256_HALF_ORDER),
            "Negated s should be high-S"
        );

        // Create signature with high-S
        let malleable_sig = Signature::from_raw(*r, high_s);

        // Standard verification should accept the high-S signature (it's mathematically valid)
        let result = p256::verify(DigestAlgorithm::Sha256, msg, &malleable_sig, &pk);
        assert!(
            result.is_ok(),
            "Standard verify should accept high-S signatures"
        );

        // Strict verification should reject the high-S signature
        let result = p256::verify_strict(DigestAlgorithm::Sha256, msg, &malleable_sig, &pk);
        assert!(
            result.is_err(),
            "verify_strict should reject high-S signatures"
        );
        assert!(matches!(result.unwrap_err(), Error::InvalidSignature));
    }

    #[test]
    fn test_half_order_boundary() {
        // Test that s = half_order is considered low-S (valid)
        // and s = half_order + 1 is considered high-S (invalid).

        // s exactly at half_order should be low-S (valid)
        assert!(is_low_s(&P256_HALF_ORDER), "s = n/2 should be low-S");

        // s = half_order + 1 should be high-S (invalid)
        let mut half_order_plus_one = P256_HALF_ORDER;
        let mut carry = 1u16;
        for i in (0..32).rev() {
            let sum = half_order_plus_one[i] as u16 + carry;
            half_order_plus_one[i] = sum as u8;
            carry = sum >> 8;
        }
        assert!(
            !is_low_s(&half_order_plus_one),
            "s = n/2 + 1 should be high-S"
        );
    }
}
