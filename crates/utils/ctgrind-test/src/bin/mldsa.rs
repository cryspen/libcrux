use crabgrind::memcheck::{self, MemState};
use libcrux_ml_dsa::ml_dsa_44;
use std::ffi::c_void;
use std::hint::black_box;

#[inline(never)]
fn test_sign() {
    // Generate key pair with known randomness — not secret yet.
    let key_pair = ml_dsa_44::generate_key_pair(black_box([0u8; 32]));

    // The ML-DSA signing key layout (per spec): [ρ(32) | K(32) | tr(64) | s₁,s₂,t₀(rest)]
    //   ρ  = public seed for matrix A  → PUBLIC, must not be poisoned
    //   K  = signing key seed          → SECRET
    //   tr = hash of verification key  → PUBLIC, must not be poisoned
    //   s₁, s₂, t₀                    → SECRET
    //
    // Poisoning ρ or tr causes false positives in `rejection_sample_less_than_field_modulus`
    // during matrix A construction, which branches on XOF output from the public ρ.
    const SEED_FOR_A_SIZE: usize = 32; // ρ
    const SEED_FOR_SIGNING_SIZE: usize = 32; // K
    const TR_SIZE: usize = 64; // tr = hash of vk

    let sk = &key_pair.signing_key;
    let sk_bytes: &[u8] = sk.as_slice();

    // Poison K (bytes 32..64)
    let _ = memcheck::mark_memory(
        sk_bytes[SEED_FOR_A_SIZE..].as_ptr() as *const c_void,
        SEED_FOR_SIGNING_SIZE,
        MemState::Undefined,
    );
    // Poison s₁, s₂, t₀ (bytes 128..end)
    let secret_tail_offset = SEED_FOR_A_SIZE + SEED_FOR_SIGNING_SIZE + TR_SIZE;
    let _ = memcheck::mark_memory(
        sk_bytes[secret_tail_offset..].as_ptr() as *const c_void,
        sk_bytes.len() - secret_tail_offset,
        MemState::Undefined,
    );

    let message = b"test message";
    let context = b"";
    // FINDINGS: Valgrind reports two classes of violations in sign():
    //
    // 1. `infinity_norm_exceeds` (ml_dsa_generic.rs:284)
    //    The rejection check `||z||∞ ≥ γ₁ - β` where z = y + c·s₁.
    //    z depends on s₁ (secret), so this branch is inherently key-dependent.
    //    This is the Fiat-Shamir-with-aborts abort step — a known, expected
    //    property of the Dilithium/ML-DSA algorithm.
    //
    // 2. `inside_out_shuffle` (sample.rs:450) in `sample_challenge_ring_element`
    //    The Fisher-Yates shuffle that builds the sparse challenge polynomial c.
    //    The challenge input c̃ = H(μ ‖ w₁) should be public, but tainted values
    //    from z (computed in a previous loop iteration) appear to spill into the
    //    scratch memory used by the shuffle in subsequent retries.
    let mut sig = ml_dsa_44::sign(sk, message, context, black_box([0u8; 32])).unwrap();

    // Unpoison signature before use.
    let sig_bytes: &mut [u8] = sig.as_mut_slice();
    let _ = memcheck::mark_memory(
        sig_bytes.as_mut_ptr() as *mut c_void,
        sig_bytes.len(),
        MemState::Defined,
    );
    println!("mldsa44 signature: {:02x?}", &sig.as_slice()[..4]);
}

pub fn main() {
    test_sign();
}
