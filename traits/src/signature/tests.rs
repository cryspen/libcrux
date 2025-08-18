// NOTE: sign_aux, verify_aux, and signing_key are passed in as arguments. signing_key cannot
// necessarily be constructed from an array, and the values of sign_aux and verify_aux may be
// connected (e.g., sign_aux may be the salt, and verify_aux may be the salt_len).
/// Generic test for the [`arrayref`](super::arrayref) traits.
pub fn simple<
    'b,
    const SIGNING_KEY_LEN: usize,
    const VERIFICATION_KEY_LEN: usize,
    const SIGNATURE_LEN: usize,
    SignAux,
    VerifyAux,
    SigningKey,
    Signer: super::arrayref::Sign<
            SIGNING_KEY_LEN,
            SIGNATURE_LEN,
            SignAux<'b> = SignAux,
            SigningKey<'b, SIGNING_KEY_LEN> = SigningKey,
        > + super::arrayref::Verify<VERIFICATION_KEY_LEN, SIGNATURE_LEN, VerifyAux<'b> = VerifyAux>,
>(
    sign_aux: SignAux,
    verify_aux: VerifyAux,
    signing_key: SigningKey,
) {
    let payload = [0u8; 20];
    let verification_key = &[1u8; VERIFICATION_KEY_LEN];

    let mut signature = [0; SIGNATURE_LEN];

    Signer::sign(&payload, signing_key, &mut signature, sign_aux).expect("Error signing");
    Signer::verify(&payload, verification_key, &signature, verify_aux).expect("Error verifying");
}
