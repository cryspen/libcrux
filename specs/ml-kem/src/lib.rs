// This module is declared here since otherwise, hax reports the following error:
//
// The THIR body of item
// DefId(0:313 ~ hacspec_kyber[4591]::parameters::KyberFieldElement::{constant#0})
// was stolen.
//
// This is being tracked in https://github.com/hacspec/hacspec-v2/issues/27
mod parameters;

use parameters::*;
use parameters::hash_functions::*;

mod compress;
mod ind_cpa;
mod matrix;
mod ntt;
mod sampling;
mod serialize;

pub use sampling::BadRejectionSamplingRandomnessError;
pub use parameters::{MlKemParams, ML_KEM_512, ML_KEM_768, ML_KEM_1024};

/// Algorithm 16: ML-KEM.KeyGen_internal
///
/// ```plaintext
/// Input: d ∈ 𝔹³², z ∈ 𝔹³².
/// Output: encapsulation key ek ∈ 𝔹^{384k+32}.
/// Output: decapsulation key dk ∈ 𝔹^{768k+96}.
///
/// (ekₚₖₑ, dkₚₖₑ) ← K-PKE.KeyGen(d)
/// ek ← ekₚₖₑ
/// dk ← (dkₚₖₑ ‖ ek ‖ H(ek) ‖ z)
/// return (ek, dk)
/// ```
fn keygen_internal<const RANK: usize>(
    params: &MlKemParams,
    d: &[u8; 32],
    z: &[u8; 32],
) -> Result<(Vec<u8>, Vec<u8>), BadRejectionSamplingRandomnessError> {
    let (ek, dk_pke) = ind_cpa::generate_keypair::<RANK>(params, d)?;

    // dk ← (dkₚₖₑ ‖ ek ‖ H(ek) ‖ z)
    let mut dk = dk_pke;
    dk.extend_from_slice(&ek);
    dk.extend_from_slice(&H(&ek));
    dk.extend_from_slice(z);

    Ok((ek, dk))
}

/// Algorithm 17: ML-KEM.Encaps_internal
///
/// ```plaintext
/// Input: encapsulation key ek ∈ 𝔹^{384k+32}.
/// Input: m ∈ 𝔹³².
/// Output: shared key K ∈ 𝔹³².
/// Output: ciphertext c ∈ 𝔹^{32(dᵤk+dᵥ)}.
///
/// (K, r) ← G(m ‖ H(ek))
/// c ← K-PKE.Encrypt(ek, m, r)
/// return (K, c)
/// ```
fn encaps_internal<const RANK: usize>(
    params: &MlKemParams,
    ek: &[u8],
    m: &[u8; 32],
) -> Result<([u8; 32], Vec<u8>), BadRejectionSamplingRandomnessError> {
    // (K, r) ← G(m ‖ H(ek))
    let mut to_hash = Vec::new();
    to_hash.extend_from_slice(m);
    to_hash.extend_from_slice(&H(ek));
    let hashed = G(&to_hash);
    let (shared_secret, pseudorandomness) = hashed.split_at(32);

    let r: [u8; 32] = pseudorandomness[..32].try_into().unwrap();

    // c ← K-PKE.Encrypt(ek, m, r)
    let c = ind_cpa::encrypt::<RANK>(params, ek, m, &r)?;

    let mut k = [0u8; 32];
    k.copy_from_slice(shared_secret);
    Ok((k, c))
}

/// Algorithm 18: ML-KEM.Decaps_internal
///
/// ```plaintext
/// Input: decapsulation key dk ∈ 𝔹^{768k+96}.
/// Input: ciphertext c ∈ 𝔹^{32(dᵤk+dᵥ)}.
/// Output: shared key K ∈ 𝔹³².
///
/// dkₚₖₑ ← dk[0 : 384k]
/// ekₚₖₑ ← dk[384k : 768k + 32]
/// h ← dk[768k + 32 : 768k + 64]
/// z ← dk[768k + 64 : 768k + 96]
/// m′ ← K-PKE.Decrypt(dkₚₖₑ, c)
/// (K′, r′) ← G(m′ ‖ h)
/// K̃ ← J(z ‖ c)
/// c′ ← K-PKE.Encrypt(ekₚₖₑ, m′, r′)
/// if c ≠ c′ then
///     K′ ← K̃
/// end if
/// return K′
/// ```
fn decaps_internal<const RANK: usize>(
    params: &MlKemParams,
    dk: &[u8],
    c: &[u8],
) -> Result<[u8; 32], BadRejectionSamplingRandomnessError> {
    let dk_pke_size = params.dk_pke_size();
    let ek_size = params.ek_size();

    // dkₚₖₑ ← dk[0 : 384k]
    let dk_pke = &dk[..dk_pke_size];

    // ekₚₖₑ ← dk[384k : 768k + 32]
    let ek = &dk[dk_pke_size..dk_pke_size + ek_size];

    // h ← dk[768k + 32 : 768k + 64]
    let h = &dk[dk_pke_size + ek_size..dk_pke_size + ek_size + H_DIGEST_SIZE];

    // z ← dk[768k + 64 : 768k + 96]
    let z = &dk[dk_pke_size + ek_size + H_DIGEST_SIZE..];

    // m′ ← K-PKE.Decrypt(dkₚₖₑ, c)
    let m_prime = ind_cpa::decrypt::<RANK>(params, dk_pke, c);

    // (K′, r′) ← G(m′ ‖ h)
    let mut to_hash = Vec::new();
    to_hash.extend_from_slice(&m_prime);
    to_hash.extend_from_slice(h);
    let hashed = G(&to_hash);
    let (success_shared_secret, pseudorandomness) = hashed.split_at(32);

    let r_prime: [u8; 32] = pseudorandomness[..32].try_into().unwrap();

    // K̃ ← J(z ‖ c)
    let mut j_input = Vec::new();
    j_input.extend_from_slice(z);
    j_input.extend_from_slice(c);
    let rejection_shared_secret: [u8; 32] = J(&j_input);

    // c′ ← K-PKE.Encrypt(ekₚₖₑ, m′, r′)
    let c_prime = ind_cpa::encrypt::<RANK>(params, ek, &m_prime, &r_prime)?;

    // if c ≠ c′ then K′ ← K̃
    if c == c_prime.as_slice() {
        let mut k = [0u8; 32];
        k.copy_from_slice(success_shared_secret);
        Ok(k)
    } else {
        Ok(rejection_shared_secret)
    }
}

/// Algorithm 19: ML-KEM.KeyGen
///
/// Generates an encapsulation key and a corresponding decapsulation key.
pub fn generate_keypair<const RANK: usize>(
    params: &MlKemParams,
    randomness: &[u8; 64],
) -> Result<(Vec<u8>, Vec<u8>), BadRejectionSamplingRandomnessError> {
    let d: &[u8; 32] = randomness[..32].try_into().unwrap();
    let z: &[u8; 32] = randomness[32..].try_into().unwrap();
    keygen_internal::<RANK>(params, d, z)
}

/// Modulus check for encapsulation key validation (FIPS 203 Section 7.2).
///
/// Verifies that ByteEncode₁₂(ByteDecode₁₂(ek[..384k])) == ek[..384k].
fn public_key_modulus_check(params: &MlKemParams, ek: &[u8]) -> bool {
    let t_size = params.t_as_ntt_encoded_size();
    let encoded_ring_elements = &ek[..t_size];

    // Decode and re-encode; the round-trip should be identity for valid keys
    for chunk in encoded_ring_elements.chunks(BYTES_PER_RING_ELEMENT) {
        let decoded = serialize::byte_decode::<{32*12}, {256*12}>(
            chunk.try_into().unwrap(), 12,
        );
        let re_encoded = serialize::byte_encode::<{32*12}, {256*12}>(decoded, 12);
        if chunk != re_encoded.as_slice() {
            return false;
        }
    }
    true
}

/// Algorithm 20: ML-KEM.Encaps
///
/// Uses the encapsulation key to generate a shared key and ciphertext.
/// Includes modulus check on ek per FIPS 203 Section 7.2.
pub fn encapsulate<const RANK: usize>(
    params: &MlKemParams,
    ek: &[u8],
    m: &[u8; 32],
) -> Result<([u8; 32], Vec<u8>), BadRejectionSamplingRandomnessError> {
    // Type check
    assert_eq!(ek.len(), params.ek_size(), "invalid encapsulation key length");
    // Modulus check
    assert!(public_key_modulus_check(params, ek), "encapsulation key modulus check failed");

    encaps_internal::<RANK>(params, ek, m)
}

/// Algorithm 21: ML-KEM.Decaps
///
/// Uses the decapsulation key to produce a shared key from a ciphertext.
pub fn decapsulate<const RANK: usize>(
    params: &MlKemParams,
    dk: &[u8],
    c: &[u8],
) -> Result<[u8; 32], BadRejectionSamplingRandomnessError> {
    decaps_internal::<RANK>(params, dk, c)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keygen_encaps_decaps_consistency() {
        let randomness = [42u8; 64];
        let (ek, dk) = generate_keypair::<3>(&ML_KEM_768, &randomness).unwrap();

        let m = [0xABu8; 32];
        let (shared_secret, ciphertext) = encapsulate::<3>(&ML_KEM_768, &ek, &m).unwrap();

        let shared_secret_decapsulated = decapsulate::<3>(&ML_KEM_768, &dk, &ciphertext).unwrap();

        assert_eq!(shared_secret, shared_secret_decapsulated);
    }

    #[test]
    fn modified_ciphertext_implicit_rejection() {
        let randomness = [1u8; 64];
        let (ek, dk) = generate_keypair::<3>(&ML_KEM_768, &randomness).unwrap();

        let m = [0x55u8; 32];
        let (shared_secret, mut ciphertext) = encapsulate::<3>(&ML_KEM_768, &ek, &m).unwrap();

        // Tamper with ciphertext
        ciphertext[0] ^= 0xFF;

        let shared_secret_decapsulated = decapsulate::<3>(&ML_KEM_768, &dk, &ciphertext).unwrap();

        assert_ne!(shared_secret, shared_secret_decapsulated);

        // Verify implicit rejection: K̃ = J(z ‖ c)
        let dk_pke_size = ML_KEM_768.dk_pke_size();
        let ek_size = ML_KEM_768.ek_size();
        let z = &dk[dk_pke_size + ek_size + H_DIGEST_SIZE..];
        let mut j_input = Vec::new();
        j_input.extend_from_slice(z);
        j_input.extend_from_slice(&ciphertext);
        let expected_rejection: [u8; 32] = J(&j_input);
        assert_eq!(shared_secret_decapsulated, expected_rejection);
    }

    #[test]
    fn modified_secret_key() {
        let randomness = [3u8; 64];
        let (ek, mut dk) = generate_keypair::<3>(&ML_KEM_768, &randomness).unwrap();

        let m = [0x77u8; 32];
        let (shared_secret, ciphertext) = encapsulate::<3>(&ML_KEM_768, &ek, &m).unwrap();

        // Tamper with the secret key (not the z portion)
        dk[0] ^= 0xFF;

        let shared_secret_decapsulated = decapsulate::<3>(&ML_KEM_768, &dk, &ciphertext).unwrap();
        assert_ne!(shared_secret, shared_secret_decapsulated);
    }
}
