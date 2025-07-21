pub trait Digest<const OUTPUT_LEN: usize> {
    type IncrementalState: Default;

    /// Oneshot API
    fn hash(digest: &mut [u8; OUTPUT_LEN], payload: &[u8]);

    // TODO: don't panic?
    fn update(state: &mut Self::IncrementalState, payload: &[u8]);

    fn finish(state: &mut Self::IncrementalState, digest: &mut [u8; OUTPUT_LEN]);

    fn reset(state: &mut Self::IncrementalState);
}
