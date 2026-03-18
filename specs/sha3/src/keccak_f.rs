/// Keccak-f[1600] permutation — FIPS 202, Section 3.3.
///
/// The state is a 5×5 array of 64-bit lanes stored as a flat `[u64; 25]`.
/// Lane `A[x, y]` maps to flat index `5*x + y`, following FIPS 202 notation.

use crate::createi;

/// Keccak-f[1600] state: 5×5 lanes of 64-bit words.
pub(crate) type State = [u64; 25];

/// Read lane `A[x, y]`.
#[inline]
#[hax_lib::requires(x < 5 && y < 5)]
fn get(state: &State, x: usize, y: usize) -> u64 {
    state[5 * x + y]
}

// =========================================================================
// Constants — FIPS 202, Section 3.3 / Algorithm 5
// =========================================================================

/// Round constants `RC[ir]` for `ir = 0..23` — FIPS 202, Algorithm 5.
const ROUND_CONSTANTS: [u64; 24] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808A,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808B,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008A,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000A,
    0x0000_0000_8000_808B,
    0x8000_0000_0000_008B,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800A,
    0x8000_0000_8000_000A,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

/// Rotation offsets for ρ step — FIPS 202, Algorithm 2 / Table 2.
///
/// Indexed as `RHO_OFFSETS[5*x + y]`.
const RHO_OFFSETS: [u32; 25] = [
    //  y=0  y=1  y=2  y=3  y=4
         0,  36,   3,  41,  18, // x = 0
         1,  44,  10,  45,   2, // x = 1
        62,   6,  43,  15,  61, // x = 2
        28,  55,  25,  21,  56, // x = 3
        27,  20,  39,   8,  14, // x = 4
];

// =========================================================================
// The five step mappings — FIPS 202, Algorithms 1–6
// =========================================================================

/// θ step — FIPS 202, Algorithm 1.
///
///   C[x]    = A[x,0] ⊕ A[x,1] ⊕ A[x,2] ⊕ A[x,3] ⊕ A[x,4]
///   D[x]    = C[x−1 mod 5] ⊕ rot(C[x+1 mod 5], 1)
///   A′[x,y] = A[x,y] ⊕ D[x]
fn theta(state: State) -> State {
    let c: [u64; 5] = createi(|x| {
        get(&state, x, 0) ^ get(&state, x, 1) ^ get(&state, x, 2)
            ^ get(&state, x, 3) ^ get(&state, x, 4)
    });
    let d: [u64; 5] = createi(|x| {
        c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1)
    });
    createi(|idx| state[idx] ^ d[idx / 5])
}

/// ρ step — FIPS 202, Algorithm 2.
///
///   A′[x,y] = rot(A[x,y], offset(x,y))
fn rho(state: State) -> State {
    createi(|idx| {
        state[idx].rotate_left(RHO_OFFSETS[idx])
    })
}

/// π step — FIPS 202, Algorithm 3.
///
///   A′[x,y] = A[(x + 3y) mod 5, x]
fn pi(state: State) -> State {
    createi(|idx| {
        let x = idx / 5;
        let y = idx % 5;
        get(&state, (x + 3 * y) % 5, x)
    })
}

/// χ step — FIPS 202, Algorithm 4.
///
///   A′[x,y] = A[x,y] ⊕ (¬A[(x+1) mod 5, y] ∧ A[(x+2) mod 5, y])
fn chi(state: State) -> State {
    createi(|idx| {
        let x = idx / 5;
        let y = idx % 5;
        get(&state, x, y)
            ^ (!get(&state, (x + 1) % 5, y) & get(&state, (x + 2) % 5, y))
    })
}

/// ι step — FIPS 202, Algorithm 6.
///
///   A′[0,0] = A[0,0] ⊕ RC[ir]
#[hax_lib::requires(round < 24)]
fn iota(mut state: State, round: usize) -> State {
    state[0] ^= ROUND_CONSTANTS[round];
    state
}

// =========================================================================
// Keccak-f[1600] — FIPS 202, Algorithm 7
// =========================================================================

/// Keccak-f[1600] permutation — FIPS 202, Algorithm 7.
///
///   Rnd(A, ir) = ι(χ(π(ρ(θ(A)))), ir)
pub(crate) fn keccak_f(mut state: State) -> State {
    for round in 0..24 {
        state = iota(chi(pi(rho(theta(state)))), round);
    }
    state
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keccak_f_all_zeros() {
        // Known answer: after Keccak-f on the all-zero state, lane (0,0) has
        // a specific value that serves as a sanity check.
        let state = [0u64; 25];
        let result = keccak_f(state);
        assert_eq!(result[0], 0xF1258F7940E1DDE7);
    }

    #[test]
    fn keccak_f_all_ones() {
        let state = [0xFFFFFFFFFFFFFFFFu64; 25];
        let result = keccak_f(state);
        assert_ne!(result, state);
    }
}
