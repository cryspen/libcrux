/// Sponge construction — FIPS 202, Algorithm 8 (KECCAK[c])
/// with pad10*1 padding — FIPS 202, Algorithm 9.
use crate::keccak_f::{keccak_f, State};

/// Map byte-lane index `l` to the flat state array index.
///
/// FIPS 202 Section 3.1.2 defines how a bit string maps onto the state array.
/// In the byte-oriented convention used by the reference implementation,
/// byte-lane `l` maps to `A[l % 5, l / 5]` = `state[5*(l%5) + l/5]`.
#[inline]
#[hax_lib::requires(l < 25)]
pub fn lane_index(l: usize) -> usize {
    5 * (l % 5) + l / 5
}

/// XOR a block of message bytes into the state (little-endian, lane-interleaved).
///
/// Corresponds to the `S ⊕ (Pi || 0^c)` step of Algorithm 8.
#[hax_lib::requires(rate <= 200 && rate % 8 == 0 && block.len() >= rate)]
pub fn xor_block_into_state(mut state: State, block: &[u8], rate: usize) -> State {
    for i in 0..(rate / 8) {
        let offset = 8 * i;
        let lane_val = u64::from_le_bytes([
            block[offset],
            block[offset + 1],
            block[offset + 2],
            block[offset + 3],
            block[offset + 4],
            block[offset + 5],
            block[offset + 6],
            block[offset + 7],
        ]);
        let idx = lane_index(i);
        state[idx] ^= lane_val;
    }
    state
}

/// Extract `len` bytes from the rate portion of the state (little-endian, lane-interleaved).
///
/// Corresponds to `Trunc_r(S)` in Algorithm 8.
#[hax_lib::fstar::options("--z3rlimit 500")]
#[hax_lib::requires(len <= 200 && output.len() >= len && out_offset <= output.len() - len)]
#[hax_lib::ensures(|_| future(output).len() == output.len())]
pub fn squeeze_state(state: &State, output: &mut [u8], out_offset: usize, len: usize) {
    let _orig_len = output.len();
    let full_lanes = len / 8;
    for i in 0..full_lanes {
        hax_lib::loop_invariant!(|i: usize| output.len() == _orig_len);
        let idx = lane_index(i);
        let bytes = state[idx].to_le_bytes();
        for b in 0..8 {
            hax_lib::loop_invariant!(|b: usize| output.len() == _orig_len);
            output[out_offset + 8 * i + b] = bytes[b];
        }
    }
    let remaining = len % 8;
    if remaining > 0 {
        let idx = lane_index(full_lanes);
        let bytes = state[idx].to_le_bytes();
        for b in 0..remaining {
            hax_lib::loop_invariant!(|b: usize| output.len() == _orig_len);
            output[out_offset + 8 * full_lanes + b] = bytes[b];
        }
    }
}

/// Keccak sponge — FIPS 202, Algorithm 8 combined with pad10*1 (Algorithm 9).
///
/// 1. Absorb: split `message` into `rate`-byte blocks, XOR each into the
///    state, and apply Keccak-f. The final partial block is padded with
///    the domain separation byte `delim` and the pad10*1 terminator `0x80`.
/// 2. Squeeze: extract `OUTPUT_LEN` bytes from the state, applying
///    Keccak-f between each `rate`-byte block of output.
///
/// The `OUTPUT_LEN < usize::MAX - 200` precondition is a Rust implementation
/// artifact to prevent arithmetic overflow; FIPS 202 places no upper bound
/// on the output length.
#[hax_lib::fstar::options("--z3rlimit 500")]
#[hax_lib::requires(rate > 0 && rate <= 200 && rate % 8 == 0 && OUTPUT_LEN < usize::MAX - 200)]
pub fn keccak<const OUTPUT_LEN: usize>(rate: usize, delim: u8, message: &[u8]) -> [u8; OUTPUT_LEN] {
    let mut state: State = [0u64; 25];

    // --- Absorb full blocks (Algorithm 8, step 6) ---
    let num_full_blocks = message.len() / rate;
    for block_idx in 0..num_full_blocks {
        let offset = block_idx * rate;
        state = xor_block_into_state(state, &message[offset..offset + rate], rate);
        state = keccak_f(state);
    }

    // --- Pad final block (Algorithm 9: pad10*1) ---
    let mut last_block = [0u8; 200];
    let remaining = message.len() - num_full_blocks * rate;
    for i in 0..remaining {
        last_block[i] = message[num_full_blocks * rate + i];
    }
    last_block[remaining] = delim; // domain separation + first bit of pad
    last_block[rate - 1] |= 0x80; // last bit of pad10*1

    state = xor_block_into_state(state, &last_block, rate);
    state = keccak_f(state);

    // --- Squeeze (Algorithm 8, steps 8–9) ---
    let mut output = [0u8; OUTPUT_LEN];
    let mut offset = 0;

    for _squeeze_round in 0..((OUTPUT_LEN + rate - 1) / rate) {
        hax_lib::loop_invariant!(|_squeeze_round: usize| offset <= OUTPUT_LEN);
        let to_copy = if OUTPUT_LEN - offset < rate {
            OUTPUT_LEN - offset
        } else {
            rate
        };
        squeeze_state(&state, &mut output, offset, to_copy);
        offset += to_copy;
        if offset < OUTPUT_LEN {
            state = keccak_f(state);
        }
    }

    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lane_index_mapping() {
        // Byte-lane l maps to A[l%5, l/5] = state[5*(l%5) + l/5]
        assert_eq!(lane_index(0), 0); // A[0,0] → 0
        assert_eq!(lane_index(1), 5); // A[1,0] → 5
        assert_eq!(lane_index(5), 1); // A[0,1] → 1
        assert_eq!(lane_index(6), 6); // A[1,1] → 6
    }
}
