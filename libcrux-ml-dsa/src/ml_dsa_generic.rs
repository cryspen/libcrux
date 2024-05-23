use crate::hash_functions::H;

pub(crate) fn generate_key_pair<
    const COLUMNS_IN_A: usize,
    const SECRET_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
>(
    randomness: [u8; 32],
) -> ([u8; SECRET_KEY_SIZE], [u8; PUBLIC_KEY_SIZE]) {
    let seed_expanded = H::<1024>(&randomness);
    let (_seed_for_matrix_a, seed_expanded) = seed_expanded.split_at(32);
    let (_seed_for_short_vectors, _random_seed_for_signing) = seed_expanded.split_at(64);

    todo!();
}
