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
        let lane_val = u64::from_le_bytes(block[offset..offset + 8].try_into().unwrap());
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
        output[out_offset + 8 * i..out_offset + 8 * (i + 1)].copy_from_slice(&bytes);
    }
    let remaining = len % 8;
    if remaining > 0 {
        let idx = lane_index(full_lanes);
        let bytes = state[idx].to_le_bytes();
        let pos = out_offset + 8 * full_lanes;
        output[pos..pos + remaining].copy_from_slice(&bytes[..remaining]);
    }
}

/// Absorb one full block: XOR it into the state, then apply Keccak-f.
///
/// Corresponds to one iteration of the absorb loop in Algorithm 8 (step 6).
#[hax_lib::requires(rate <= 200 && rate % 8 == 0 && block.len() >= rate)]
pub fn absorb_block(state: State, block: &[u8], rate: usize) -> State {
    let state = xor_block_into_state(state, block, rate);
    keccak_f(state)
}

/// Build the padded last block: copy remaining message bytes, add the
/// domain-separation byte `delim`, and set the final bit of pad10*1.
///
/// Returns a `rate`-byte buffer ready to be absorbed via `xor_block_into_state`.
#[hax_lib::fstar::options("--z3rlimit 200")]
#[hax_lib::requires(rate > 0 && rate <= 200 && rate % 8 == 0 && remaining < rate
                     && msg_offset <= message.len() && remaining <= message.len() - msg_offset)]
pub fn pad_last_block(
    message: &[u8],
    msg_offset: usize,
    remaining: usize,
    rate: usize,
    delim: u8,
) -> [u8; 200] {
    let mut buffer = [0u8; 200];
    buffer[..remaining].copy_from_slice(&message[msg_offset..msg_offset + remaining]);
    buffer[remaining] = delim;
    buffer[rate - 1] = buffer[rate - 1] | 0x80;
    buffer
}

/// Absorb the final (possibly partial) block: pad it, XOR into state, and
/// apply Keccak-f.
///
/// Combines `pad_last_block` + `absorb_block`.
#[hax_lib::fstar::options("--z3rlimit 200")]
#[hax_lib::requires(rate > 0 && rate <= 200 && rate % 8 == 0 && remaining < rate
                     && msg_offset <= message.len() && remaining <= message.len() - msg_offset)]
pub fn absorb_final(
    state: State,
    message: &[u8],
    msg_offset: usize,
    remaining: usize,
    rate: usize,
    delim: u8,
) -> State {
    let block = pad_last_block(message, msg_offset, remaining, rate, delim);
    absorb_block(state, &block, rate)
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
    for _block_idx in 0..num_full_blocks {
        let offset = _block_idx * rate;
        state = absorb_block(state, &message[offset..offset + rate], rate);
    }

    // --- Pad and absorb final block (Algorithm 9: pad10*1) ---
    let remaining = message.len() - num_full_blocks * rate;
    state = absorb_final(state, message, num_full_blocks * rate, remaining, rate, delim);

    // --- Squeeze (Algorithm 8, steps 8–9) ---
    let mut output = [0u8; OUTPUT_LEN];
    let mut offset: usize = 0;
    let num_squeeze_blocks = (OUTPUT_LEN + rate - 1) / rate;
    for _squeeze_round in 0..num_squeeze_blocks {
        hax_lib::loop_invariant!(|_squeeze_round: usize| offset <= OUTPUT_LEN);
        if _squeeze_round > 0 {
            state = keccak_f(state);
        }
        let to_copy = core::cmp::min(OUTPUT_LEN - offset, rate);
        squeeze_state(&state, &mut output, offset, to_copy);
        offset += to_copy;
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
