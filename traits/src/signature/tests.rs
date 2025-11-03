// NOTE: sign_aux, verify_aux, signing_key and verification_key are passed in as arguments. signing_key and
// verification_key cannot
// necessarily be constructed from an array, and the values of sign_aux and verify_aux may be
// connected (e.g., sign_aux may be the salt, and verify_aux may be the salt_len).
/// Generic test for the [`arrayref`](super::arrayref) traits.
pub fn simple_arrayref<
    'b,
    const SIGNING_KEY_LEN: usize,
    const VERIFICATION_KEY_LEN: usize,
    const SIGNATURE_LEN: usize,
    const RAND_KEYGEN_LEN: usize,
    SignAux,
    Signer: super::arrayref::Sign<
        SIGNING_KEY_LEN,
        VERIFICATION_KEY_LEN,
        SIGNATURE_LEN,
        RAND_KEYGEN_LEN,
        SignAux<'b> = SignAux,
    >,
>(
    sign_aux: SignAux,
) {
    use libcrux_secrets::Classify;
    let keygen_rand = [1u8; RAND_KEYGEN_LEN].classify();
    let mut signing_key = [0u8; SIGNING_KEY_LEN].classify();
    let mut verification_key = [0u8; VERIFICATION_KEY_LEN];
    Signer::keygen_derand(&mut signing_key, &mut verification_key, &keygen_rand).unwrap();

    let payload = [0u8; 20];

    let mut signature = [0; SIGNATURE_LEN];

    Signer::sign(&payload, &signing_key, &mut signature, sign_aux).expect("Error signing");
    Signer::verify(&payload, &verification_key, &signature).expect("Error verifying");
}
