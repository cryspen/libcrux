/// Sponge construction — FIPS 202, Algorithm 8 (KECCAK[c])
/// with pad10*1 padding — FIPS 202, Algorithm 9.
///
/// With the state stored as `state[5·y + x]` (FIPS 202 §3.1.2), byte-lane
/// `l` lives directly at `state[l]`, so no lane-index permutation is
/// needed here.
use crate::createi;
use crate::keccak_f::{keccak_f, State};

/// XOR a block of message bytes into the state (little-endian, lane-interleaved).
///
/// Corresponds to the `S ⊕ (Pi || 0^c)` step of Algorithm 8.
#[hax_lib::requires(rate <= 200 && rate % 8 == 0 && block.len() >= rate)]
pub fn xor_block_into_state(state: State, block: &[u8], rate: usize) -> State {
    createi(|i| {
        if i < rate / 8 {
            state[i] ^ u64::from_le_bytes(block[8 * i..8 * i + 8].try_into().unwrap())
        } else {
            state[i]
        }
    })
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
        let bytes = state[i].to_le_bytes();
        output[out_offset + 8 * i..out_offset + 8 * (i + 1)].copy_from_slice(&bytes);
    }
    let remaining = len % 8;
    if remaining > 0 {
        let bytes = state[full_lanes].to_le_bytes();
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

/// Absorb phase of the Keccak sponge (FIPS 202, Algorithm 8, step 6 combined
/// with the pad10*1 padding of Algorithm 9).
///
/// Splits `message` into `rate`-byte blocks, XORing each into the state and
/// applying Keccak-f. The final partial block is padded with the domain
/// separation byte `delim` and the pad10*1 terminator `0x80` before being
/// absorbed.
#[hax_lib::fstar::options("--z3rlimit 200")]
#[hax_lib::requires(rate > 0 && rate <= 200 && rate % 8 == 0)]
pub fn absorb(rate: usize, delim: u8, message: &[u8]) -> State {
    let mut state: State = [0u64; 25];

    // --- Absorb full blocks (Algorithm 8, step 6) ---
    let num_full_blocks = message.len() / rate;
    for _block_idx in 0..num_full_blocks {
        let offset = _block_idx * rate;
        state = absorb_block(state, &message[offset..offset + rate], rate);
    }

    // --- Pad and absorb final block (Algorithm 9: pad10*1) ---
    let remaining = message.len() - num_full_blocks * rate;
    absorb_final(
        state,
        message,
        num_full_blocks * rate,
        remaining,
        rate,
        delim,
    )
}

/// Squeeze phase of the Keccak sponge (FIPS 202, Algorithm 8, steps 8–9).
///
/// Extracts `OUTPUT_LEN` bytes from `state`, applying Keccak-f between each
/// `rate`-byte block of output.
///
/// Structure chosen to mirror the libcrux impl (`keccak1` in
/// `crates/algorithms/sha3/src/generic_keccak/portable.rs`) so the F*
/// equivalence proof can line the two sides up iteration-for-iteration.
#[hax_lib::fstar::options("--z3rlimit 500")]
#[hax_lib::requires(rate > 0 && rate <= 200 && rate % 8 == 0 && OUTPUT_LEN < usize::MAX - 200)]
pub fn squeeze<const OUTPUT_LEN: usize>(mut state: State, rate: usize) -> [u8; OUTPUT_LEN] {
    let mut output = [0u8; OUTPUT_LEN];
    let output_blocks = OUTPUT_LEN / rate;
    let output_rem = OUTPUT_LEN % rate;
    if output_blocks == 0 {
        squeeze_state(&state, &mut output, 0, OUTPUT_LEN);
    } else {
        squeeze_state(&state, &mut output, 0, rate);
        for i in 1..output_blocks {
            state = keccak_f(state);
            squeeze_state(&state, &mut output, i * rate, rate);
        }
        if output_rem != 0 {
            state = keccak_f(state);
            squeeze_state(&state, &mut output, OUTPUT_LEN - output_rem, output_rem);
        }
    }

    output
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
#[hax_lib::requires(rate > 0 && rate <= 200 && rate % 8 == 0 && OUTPUT_LEN < usize::MAX - 200)]
pub fn keccak<const OUTPUT_LEN: usize>(rate: usize, delim: u8, message: &[u8]) -> [u8; OUTPUT_LEN] {
    squeeze::<OUTPUT_LEN>(absorb(rate, delim, message), rate)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every SHA-3 variant must satisfy `keccak == squeeze ∘ absorb`.
    /// This pins down the refactor that split `keccak` into its two
    /// phases so the F* equivalence proof can be structured per-phase.
    #[test]
    fn keccak_equals_squeeze_of_absorb() {
        fn check<const OUT: usize>(rate: usize, delim: u8, msg: &[u8]) {
            let via_keccak: [u8; OUT] = keccak::<OUT>(rate, delim, msg);
            let via_split: [u8; OUT] = squeeze::<OUT>(absorb(rate, delim, msg), rate);
            assert_eq!(
                via_keccak,
                via_split,
                "keccak != squeeze(absorb) for rate={rate}, delim={delim:#x}, msg.len()={}",
                msg.len()
            );
        }

        let empty: [u8; 0] = [];
        let short = b"hello world";
        let long: Vec<u8> = (0u8..200).collect();

        // SHA3-224: rate=144, delim=0x06, out=28
        check::<28>(144, 0x06, &empty);
        check::<28>(144, 0x06, short);
        check::<28>(144, 0x06, &long);
        // SHA3-256: rate=136, delim=0x06, out=32
        check::<32>(136, 0x06, &empty);
        check::<32>(136, 0x06, short);
        check::<32>(136, 0x06, &long);
        // SHA3-384: rate=104, delim=0x06, out=48
        check::<48>(104, 0x06, short);
        // SHA3-512: rate=72, delim=0x06, out=64
        check::<64>(72, 0x06, short);
        // SHAKE128: rate=168, delim=0x1f — short and long output exercise the squeeze loop.
        check::<16>(168, 0x1f, short);
        check::<200>(168, 0x1f, short);
        // SHAKE256: rate=136, delim=0x1f.
        check::<64>(136, 0x1f, short);
        check::<300>(136, 0x1f, short);
    }
}
