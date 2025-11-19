pub fn simple<
    const OUTPUT_LEN: usize,
    IncrementalState,
    HashImplementation: super::arrayref::DigestIncremental<OUTPUT_LEN, IncrementalState = IncrementalState>
        + super::arrayref::Hash<OUTPUT_LEN>,
>(
    // provide the state, since not all states currently implement `Default`
    state: IncrementalState,
) {
    let payload = &[1, 2, 3, 4, 5];

    // oneshot API
    let mut digest_oneshot = [0u8; OUTPUT_LEN];
    HashImplementation::hash(&mut digest_oneshot, payload).unwrap();

    // incremental API
    let mut digest_incremental = [0u8; OUTPUT_LEN];
    let mut hasher = super::Hasher::<OUTPUT_LEN, HashImplementation> { state };
    hasher.update(payload).unwrap();
    hasher.finish(&mut digest_incremental);

    // ensure same
    assert_eq!(digest_oneshot, digest_incremental);
}
