use crate::{
    constants::COEFFICIENTS_IN_RING_ELEMENT, encoding, ml_dsa_generic::Signature,
    polynomial::PolynomialRingElement, simd::traits::Operations, VerificationError,
};

impl<
        SIMDUnit: Operations,
        const COMMITMENT_HASH_SIZE: usize,
        const COLUMNS_IN_A: usize,
        const ROWS_IN_A: usize,
    > Signature<SIMDUnit, COMMITMENT_HASH_SIZE, COLUMNS_IN_A, ROWS_IN_A>
{
    #[allow(non_snake_case)]
    #[inline(always)]
    pub(crate) fn serialize<
        const GAMMA1_EXPONENT: usize,
        const GAMMA1_RING_ELEMENT_SIZE: usize,
        const MAX_ONES_IN_HINT: usize,
        const SIGNATURE_SIZE: usize,
    >(
        &self,
    ) -> [u8; SIGNATURE_SIZE] {
        let mut signature = [0u8; SIGNATURE_SIZE];
        let mut offset = 0;

        signature[offset..offset + COMMITMENT_HASH_SIZE].copy_from_slice(&self.commitment_hash);
        offset += COMMITMENT_HASH_SIZE;

        for i in 0..COLUMNS_IN_A {
            signature[offset..offset + GAMMA1_RING_ELEMENT_SIZE].copy_from_slice(
                &encoding::gamma1::serialize::<SIMDUnit, GAMMA1_EXPONENT, GAMMA1_RING_ELEMENT_SIZE>(
                    self.signer_response[i],
                ),
            );
            offset += GAMMA1_RING_ELEMENT_SIZE;
        }

        let mut true_hints_seen = 0;

        // Unfortunately the following does not go through hax:
        //
        //     let hint_serialized = &mut signature[offset..];
        //
        // Instead, we have to mutate signature[offset + ..] directly.
        for i in 0..ROWS_IN_A {
            for (j, hint) in self.hint[i].into_iter().enumerate() {
                if hint == 1 {
                    signature[offset + true_hints_seen] = j as u8;
                    true_hints_seen += 1;
                }
            }
            signature[offset + MAX_ONES_IN_HINT + i] = true_hints_seen as u8;
        }

        signature
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    pub(crate) fn deserialize<
        const GAMMA1_EXPONENT: usize,
        const GAMMA1_RING_ELEMENT_SIZE: usize,
        const MAX_ONES_IN_HINT: usize,
        const SIGNATURE_SIZE: usize,
    >(
        serialized: &[u8; SIGNATURE_SIZE],
    ) -> Result<Self, VerificationError> {
        let (commitment_hash, rest_of_serialized) = serialized.split_at(COMMITMENT_HASH_SIZE);
        let (signer_response_serialized, hint_serialized) =
            rest_of_serialized.split_at(GAMMA1_RING_ELEMENT_SIZE * COLUMNS_IN_A);

        let mut signer_response = [PolynomialRingElement::<SIMDUnit>::ZERO(); COLUMNS_IN_A];

        for i in 0..COLUMNS_IN_A {
            signer_response[i] = encoding::gamma1::deserialize::<SIMDUnit, GAMMA1_EXPONENT>(
                &signer_response_serialized
                    [i * GAMMA1_RING_ELEMENT_SIZE..(i + 1) * GAMMA1_RING_ELEMENT_SIZE],
            );
        }

        // While there are several ways to encode the same hint vector, we
        // allow only one such encoding, to ensure strong unforgeability.
        let mut hint = [[0; COEFFICIENTS_IN_RING_ELEMENT]; ROWS_IN_A];

        let mut previous_true_hints_seen = 0usize;

        let mut i = 0;
        let mut malformed_hint = false;

        while i < ROWS_IN_A && !malformed_hint {
            let current_true_hints_seen = hint_serialized[MAX_ONES_IN_HINT + i] as usize;

            if (current_true_hints_seen < previous_true_hints_seen)
                || (previous_true_hints_seen > MAX_ONES_IN_HINT)
            {
                // the true hints seen should be increasing
                malformed_hint = true;
            }

            let mut j = previous_true_hints_seen;
            while !malformed_hint && j < current_true_hints_seen {
                if j > previous_true_hints_seen && hint_serialized[j] <= hint_serialized[j - 1] {
                    // indices of true hints for a specific polynomial should be
                    // increasing
                    malformed_hint = true;
                }
                if !malformed_hint {
                    hint[i][hint_serialized[j] as usize] = 1;
                    j += 1;
                }
            }

            if !malformed_hint {
                previous_true_hints_seen = current_true_hints_seen;
                i += 1;
            }
        }

        i = previous_true_hints_seen;
        while i < MAX_ONES_IN_HINT && !malformed_hint {
            if hint_serialized[i] != 0 {
                // ensures padding indices are zero
                malformed_hint = true;
            }
            i += 1;
        }

        if malformed_hint {
            Err(VerificationError::MalformedHintError)
        } else {
            Ok(Signature {
                commitment_hash: commitment_hash.try_into().unwrap(),
                signer_response,
                hint,
            })
        }
    }
}
