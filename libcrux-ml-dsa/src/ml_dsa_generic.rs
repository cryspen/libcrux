pub(crate) fn generate_key_pair<const SECRET_KEY_SIZE: usize, const PUBLIC_KEY_SIZE: usize>(
    randomness: [u8; 32],
) -> ([u8; SECRET_KEY_SIZE], [u8; PUBLIC_KEY_SIZE]) {
    let _ = randomness;
    todo!();
}
