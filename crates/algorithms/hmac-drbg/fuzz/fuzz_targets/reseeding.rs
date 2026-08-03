//! Fuzz the auto-reseeding wrappers `HmacSha256DrbgRng`, `HmacSha384DrbgRng`
//! and `HmacSha512DrbgRng`.
//!
//! These wrap `HmacDrbg` in the *infallible* `rand::CryptoRng` interface, so
//! every error the inner DRBG can return is handled internally: either by
//! reseeding from the inner RNG, or by an `unreachable!()`. This target is
//! therefore mainly a hunt for inputs that reach one of those `unreachable!()`s,
//! plus a check of the reseed counter against the model in `expect_counter`.
//!
//! Input layout (every field is zero-padded when the input ends early, so short
//! inputs are valid):
//!   [0]       algorithm selector: 0 → SHA-256, 1 → SHA-384, 2 → SHA-512
//!   [1]       constructor: even → `new_from_seed`, odd → `new`
//!   [2..10]   seed for the reseed RNG (little-endian u64)
//!   [10..42]  entropy         (`new_from_seed` only)
//!   [42..74]  nonce           (`new_from_seed` only)
//!   [74..106] personalization
//!   [106..]   operation stream, each record starting with a tag byte:
//!     tag % 4 == 0  `next_u32`
//!     tag % 4 == 1  `next_u64`
//!     tag % 4 == 2  `fill_bytes`; [1] = length class, [2..6] = raw length
//!     tag % 4 == 3  jump the reseed counter to the `RESEED_INTERVAL` boundary;
//!                   [1] selects which side of it
//!
//! Every operation runs against two identically seeded wrappers, so that output
//! can be checked by comparison instead of against a probabilistic property.
//!
//! Checks:
//!   - No panic or undefined behaviour for any input.
//!   - The reseed counter follows `expect_counter`: every generated block
//!     increments it, and a block requested while the counter is past
//!     `RESEED_INTERVAL` reseeds first (resetting it to 1) rather than failing.
//!     This is what distinguishes these wrappers from plain `HmacDrbg`, whose
//!     `generate` would return `ReseedRequired` instead.
//!   - The two wrappers agree on every byte of output, for every request size.
//!     Since their `fill_bytes` buffers start pre-filled with *different*
//!     sentinels, any byte the wrapper fails to write shows up as a mismatch —
//!     including in requests too short for an "output is not all sentinel"
//!     check to be usable (a 1-byte request is legitimately all-sentinel one
//!     time in 256).
#![no_main]

use libcrux_hmac_drbg::{
    HmacSha256DrbgRng, HmacSha384DrbgRng, HmacSha512DrbgRng, MAX_GENERATE_BYTES, RESEED_INTERVAL,
};
use libfuzzer_sys::fuzz_target;
use rand::{rngs::StdRng, Rng, SeedableRng};

/// A cursor over the fuzz input that zero-pads once the data runs out.
struct Cursor<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    fn new(data: &'a [u8]) -> Self {
        Self { data, pos: 0 }
    }

    /// The next byte, or `None` once the input is exhausted. Used for the
    /// operation tags, where running out ends the stream.
    fn byte(&mut self) -> Option<u8> {
        let b = self.data.get(self.pos)?;
        self.pos += 1;
        Some(*b)
    }

    /// The next byte, or 0 once the input is exhausted.
    fn byte_or_zero(&mut self) -> u8 {
        self.byte().unwrap_or(0)
    }

    /// The next `N` bytes, zero-padded once the input is exhausted.
    fn array<const N: usize>(&mut self) -> [u8; N] {
        let mut out = [0u8; N];
        for b in out.iter_mut() {
            *b = self.byte_or_zero();
        }
        out
    }

    fn u32_le(&mut self) -> u32 {
        u32::from_le_bytes(self.array::<4>())
    }
}

/// Model of the reseed counter after `blocks` calls to
/// `HmacDrbgRng::safe_generate_small`: each call reseeds first (counter → 1)
/// when the counter is past the interval, then increments it.
fn expect_counter(mut counter: u64, blocks: usize) -> u64 {
    for _ in 0..blocks {
        if counter > RESEED_INTERVAL {
            counter = 1;
        }
        counter += 1;
    }
    counter
}

/// Pick a `fill_bytes` length. Most requests stay small so that execution stays
/// cheap, while class 3 covers the `MAX_GENERATE_BYTES` chunking boundary and
/// the multi-chunk case.
fn pick_len(class: u8, raw: u32) -> usize {
    match class % 4 {
        0 | 1 => (raw % 256) as usize,
        2 => (raw % 8192) as usize,
        _ => MAX_GENERATE_BYTES - 2 + (raw % (MAX_GENERATE_BYTES as u32 + 6)) as usize,
    }
}

/// Sentinels the two output buffers are pre-filled with. They must differ, so
/// that a byte left unwritten by `fill_bytes` differs between the buffers.
const SENTINEL_A: u8 = 0xaa;
const SENTINEL_B: u8 = 0x55;

/// Runs the operation stream against two identically seeded `$alias` wrappers.
///
/// Takes the type alias rather than a constructed wrapper because the two
/// replicas have to be built the same way, and because `HmacDrbgRng`'s
/// `HmacAlgorithm` bound is crate-private — a generic function over it can't be
/// written from outside the crate.
macro_rules! run_reseeding {
    ($alias:ident, $cur:expr, $from_seed:expr, $seed:expr, $entropy:expr, $nonce:expr, $pers:expr) => {{
        let cur = &mut $cur;
        let make_reseeding_rng = || StdRng::seed_from_u64($seed);
        let (mut rng_a, mut rng_b) = if $from_seed {
            (
                $alias::new_from_seed(make_reseeding_rng(), $entropy, $nonce, $pers),
                $alias::new_from_seed(make_reseeding_rng(), $entropy, $nonce, $pers),
            )
        } else {
            (
                $alias::new(make_reseeding_rng(), $pers),
                $alias::new(make_reseeding_rng(), $pers),
            )
        };

        // Bound iterations so the fuzzer doesn't get stuck in long loops.
        const MAX_OPS: usize = 16;

        for _ in 0..MAX_OPS {
            let tag = match cur.byte() {
                Some(b) => b,
                None => break,
            };

            match tag % 4 {
                // next_u32 / next_u64: one generated block each.
                0 | 1 => {
                    let before = rng_a.reseed_counter();
                    if tag % 4 == 0 {
                        assert_eq!(rng_a.next_u32(), rng_b.next_u32());
                    } else {
                        assert_eq!(rng_a.next_u64(), rng_b.next_u64());
                    }
                    let expected = expect_counter(before, 1);
                    assert_eq!(rng_a.reseed_counter(), expected);
                    assert_eq!(rng_b.reseed_counter(), expected);
                }

                // fill_bytes
                2 => {
                    let class = cur.byte_or_zero();
                    let len = pick_len(class, cur.u32_le());

                    let before = rng_a.reseed_counter();
                    let mut out_a = vec![SENTINEL_A; len];
                    let mut out_b = vec![SENTINEL_B; len];
                    rng_a.fill_bytes(&mut out_a);
                    rng_b.fill_bytes(&mut out_b);

                    // Reporting the first differing index keeps the failure
                    // readable — the buffers can be 64 KiB or more.
                    if let Some(i) = out_a.iter().zip(&out_b).position(|(a, b)| a != b) {
                        panic!(
                            "fill_bytes({len}): byte {i} differs ({:#04x} vs {:#04x}) — \
                             left unwritten, or output is not deterministic",
                            out_a[i], out_b[i]
                        );
                    }

                    // One block per full chunk, plus one for the remainder.
                    let blocks = len / MAX_GENERATE_BYTES + 1;
                    let expected = expect_counter(before, blocks);
                    assert_eq!(rng_a.reseed_counter(), expected);
                    assert_eq!(rng_b.reseed_counter(), expected);
                }

                // Jump the counter to the reseed boundary, which generating
                // cannot reach (RESEED_INTERVAL is 2^48).
                _ => {
                    let counter = match cur.byte_or_zero() % 4 {
                        0 => RESEED_INTERVAL - 1,
                        1 => RESEED_INTERVAL,
                        2 => RESEED_INTERVAL + 1,
                        _ => u64::MAX,
                    };
                    rng_a.set_reseed_counter(counter);
                    rng_b.set_reseed_counter(counter);
                    assert_eq!(rng_a.reseed_counter(), counter);
                    assert_eq!(rng_b.reseed_counter(), counter);
                }
            }
        }
    }};
}

fuzz_target!(|data: &[u8]| {
    let mut cur = Cursor::new(data);

    let alg = cur.byte_or_zero() % 3;
    let from_seed = cur.byte_or_zero() % 2 == 0;
    let seed = u64::from_le_bytes(cur.array::<8>());
    let entropy = cur.array::<32>();
    let nonce = cur.array::<32>();
    let pers = cur.array::<32>();

    match alg {
        0 => run_reseeding!(
            HmacSha256DrbgRng,
            cur,
            from_seed,
            seed,
            &entropy,
            &nonce,
            &pers
        ),
        1 => run_reseeding!(
            HmacSha384DrbgRng,
            cur,
            from_seed,
            seed,
            &entropy,
            &nonce,
            &pers
        ),
        _ => run_reseeding!(
            HmacSha512DrbgRng,
            cur,
            from_seed,
            seed,
            &entropy,
            &nonce,
            &pers
        ),
    }
});
