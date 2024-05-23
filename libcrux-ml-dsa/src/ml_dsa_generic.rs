use crate::{hash_functions::H, matrix::expand_to_A, utils::into_padded_array};

#[allow(non_snake_case)]
pub(crate) fn generate_key_pair<
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
    const SECRET_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
>(
    randomness: [u8; 32],
) -> ([u8; SECRET_KEY_SIZE], [u8; PUBLIC_KEY_SIZE]) {
    let seed_expanded = H::<1024>(&randomness);
    let (seed_for_A, seed_expanded) = seed_expanded.split_at(32);
    let (_seed_for_short_vectors, _random_seed_for_signing) = seed_expanded.split_at(64);

    let _A_hat = expand_to_A::<ROWS_IN_A, COLUMNS_IN_A>(into_padded_array(seed_for_A), false);

    todo!();
}
