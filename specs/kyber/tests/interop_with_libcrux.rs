//! Test spec - code interop

use hacspec_kyber::{
    KYBER768_CIPHERTEXT_SIZE, KYBER768_KEY_GENERATION_SEED_SIZE, KYBER768_SHARED_SECRET_SIZE,
};
use libcrux_kem::MlKemCiphertext;
use rand::{rngs::OsRng, RngCore};

#[test]
fn same_inputs_result_in_same_output() {
    let mut keygen_seed = [0u8; KYBER768_KEY_GENERATION_SEED_SIZE];
    OsRng.fill_bytes(&mut keygen_seed);

    let spec_key_pair = hacspec_kyber::generate_keypair(keygen_seed).unwrap();
    let libcrux_key_pair =
        libcrux_kem::deterministic::mlkem768_generate_keypair_derand(keygen_seed);

    assert_eq!(libcrux_key_pair.pk(), spec_key_pair.pk());
    assert_eq!(libcrux_key_pair.sk(), spec_key_pair.sk());

    let mut message = [0u8; KYBER768_SHARED_SECRET_SIZE];
    OsRng.fill_bytes(&mut message);

    let (spec_ct, spec_ss) = hacspec_kyber::encapsulate(*spec_key_pair.pk(), message).unwrap();
    let (libcrux_ct, libcrux_ss) = libcrux_kem::deterministic::mlkem768_encapsulate_derand(
        &libcrux_key_pair.pk().into(),
        message,
    );

    assert_eq!(libcrux_ct.as_ref(), spec_ct);
    assert_eq!(libcrux_ss.as_ref(), spec_ss);

    let (spec_ct, spec_ss) = hacspec_kyber::encapsulate(*spec_key_pair.pk(), message).unwrap();
    let (libcrux_ct, libcrux_ss) = libcrux_kem::deterministic::mlkem768_encapsulate_derand(
        &libcrux_key_pair.pk().into(),
        message,
    );

    assert_eq!(libcrux_ct.as_ref(), spec_ct);
    assert_eq!(libcrux_ss.as_ref(), spec_ss);

    let spec_ss = hacspec_kyber::decapsulate(spec_ct, *spec_key_pair.sk());
    let libcrux_ss = libcrux_kem::deterministic::mlkem768_decapsulate_derand(
        libcrux_key_pair.private_key(),
        &libcrux_ct,
    );

    assert_eq!(libcrux_ss, spec_ss);
}

fn modify_ciphertext_pair(
    libcrux_ct: MlKemCiphertext<KYBER768_CIPHERTEXT_SIZE>,
    mut spec_ct: hacspec_kyber::Ciphertext,
) -> (
    MlKemCiphertext<KYBER768_CIPHERTEXT_SIZE>,
    hacspec_kyber::Ciphertext,
) {
    let mut random_bytes = [0u8; 3];
    OsRng.fill_bytes(&mut random_bytes);

    let mut byte_to_modify_with: u8 = random_bytes[0];
    if byte_to_modify_with == 0 {
        byte_to_modify_with += 1;
    }

    let random_u16 = (random_bytes[2] as usize) << 8 | random_bytes[1] as usize;
    let position = random_u16 % KYBER768_CIPHERTEXT_SIZE;

    let mut raw_libcrux_ct: [u8; KYBER768_CIPHERTEXT_SIZE] = libcrux_ct.into();
    raw_libcrux_ct[position] ^= byte_to_modify_with;

    spec_ct[position] ^= byte_to_modify_with;

    (raw_libcrux_ct.try_into().unwrap(), spec_ct)
}

#[test]
fn implicit_rejection_happens_the_same_way() {
    let mut keygen_seed = [0u8; KYBER768_KEY_GENERATION_SEED_SIZE];
    OsRng.fill_bytes(&mut keygen_seed);

    let spec_key_pair = hacspec_kyber::generate_keypair(keygen_seed).unwrap();
    let libcrux_key_pair =
        libcrux_kem::deterministic::mlkem768_generate_keypair_derand(keygen_seed);

    let mut message = [0u8; KYBER768_SHARED_SECRET_SIZE];
    OsRng.fill_bytes(&mut message);

    let (spec_ct, spec_ss) = hacspec_kyber::encapsulate(*spec_key_pair.pk(), message).unwrap();
    let (libcrux_ct, libcrux_ss) = libcrux_kem::deterministic::mlkem768_encapsulate_derand(
        &libcrux_key_pair.pk().into(),
        message,
    );

    assert_eq!(libcrux_ct.as_ref(), spec_ct);
    assert_eq!(libcrux_ss.as_ref(), spec_ss);

    let (spec_ct, _) = hacspec_kyber::encapsulate(*spec_key_pair.pk(), message).unwrap();
    let (libcrux_ct, _) = libcrux_kem::deterministic::mlkem768_encapsulate_derand(
        &libcrux_key_pair.pk().into(),
        message,
    );

    let (modified_libcrux_ct, modified_spec_ct) = modify_ciphertext_pair(libcrux_ct, spec_ct);

    let spec_ss = hacspec_kyber::decapsulate(modified_spec_ct, *spec_key_pair.sk());
    let libcrux_ss = libcrux_kem::deterministic::mlkem768_decapsulate_derand(
        libcrux_key_pair.private_key(),
        &modified_libcrux_ct,
    );

    assert_eq!(libcrux_ss, spec_ss);
}
