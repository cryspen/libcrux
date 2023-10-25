//! Test spec - code interop

use hacspec_kyber::{encapsulate, generate_keypair};
use libcrux::kem::KyberCiphertext;
use rand::{rngs::OsRng, RngCore};

#[test]
fn spec_libcrux() {
    let mut seed = [0u8; 64];
    OsRng.fill_bytes(&mut seed);
    let mut randomness = [0u8; 32];
    OsRng.fill_bytes(&mut randomness);

    let libcrux_key_pair = libcrux::kem::kyber768_generate_keypair_derand(seed).unwrap();

    // spec
    let (hacspec_ct, hacspec_ss) = encapsulate(libcrux_key_pair.pk().clone(), randomness).unwrap();

    let ciphertext = KyberCiphertext::from(hacspec_ct);
    let libcrux_ss =
        libcrux::kem::kyber768_decapsulate_derand(libcrux_key_pair.private_key(), &ciphertext);
    assert_eq!(hacspec_ss, libcrux_ss);
}

#[test]
fn libcrux_spec() {
    let mut seed = [0u8; 64];
    OsRng.fill_bytes(&mut seed);
    let mut randomness = [0u8; 32];
    OsRng.fill_bytes(&mut randomness);

    let hacspec_key_pair = generate_keypair(seed).unwrap();

    // libcrux
    let (libcrux_ct, libcrux_ss) =
        libcrux::kem::kyber768_encapsulate_derand(&hacspec_key_pair.pk().into(), randomness)
            .unwrap();

    let hacspec_ss = hacspec_kyber::decapsulate(
        libcrux_ct.as_ref().try_into().unwrap(),
        *hacspec_key_pair.sk(),
    );

    assert_eq!(hacspec_ss, libcrux_ss.as_ref());
}
