//! Test spec - code interop

use hacspec_kyber::{KYBER768_KEY_GENERATION_SEED_SIZE, KYBER768_SHARED_SECRET_SIZE, KYBER768_CIPHERTEXT_SIZE};
use rand::{rngs::OsRng, RngCore};
use libcrux::kem::KyberCiphertext;

#[test]
fn same_inputs_result_in_same_output() {
    let mut keygen_seed = [0u8; KYBER768_KEY_GENERATION_SEED_SIZE];
    OsRng.fill_bytes(&mut keygen_seed);

    let libcrux_key_pair_result = libcrux::kem::kyber768_generate_keypair_derand(keygen_seed);
    let spec_key_pair_result = hacspec_kyber::generate_keypair(keygen_seed);

    if libcrux_key_pair_result.is_err() {
        spec_key_pair_result.expect_err("If rejection sampling failed in libcrux, it should fail in the spec as well.");
        return
    }

    let libcrux_key_pair = libcrux::kem::kyber768_generate_keypair_derand(keygen_seed).unwrap();
    let spec_key_pair = hacspec_kyber::generate_keypair(keygen_seed).unwrap();

    assert_eq!(libcrux_key_pair.pk(), spec_key_pair.pk());
    assert_eq!(libcrux_key_pair.sk(), spec_key_pair.sk());

    let mut message = [0u8; KYBER768_SHARED_SECRET_SIZE];
    OsRng.fill_bytes(&mut message);

    let (libcrux_ct, libcrux_ss) = libcrux::kem::kyber768_encapsulate_derand(&libcrux_key_pair.pk().into(), message).unwrap();
    let (spec_ct, spec_ss) = hacspec_kyber::encapsulate(*spec_key_pair.pk(), message).unwrap();

    assert_eq!(libcrux_ct.as_ref(), spec_ct);
    assert_eq!(libcrux_ss.as_ref(), spec_ss);

    let (libcrux_ct, libcrux_ss) = libcrux::kem::kyber768_encapsulate_derand(&libcrux_key_pair.pk().into(), message).unwrap();
    let (spec_ct, spec_ss) = hacspec_kyber::encapsulate(*spec_key_pair.pk(), message).unwrap();

    assert_eq!(libcrux_ct.as_ref(), spec_ct);
    assert_eq!(libcrux_ss.as_ref(), spec_ss);

   let libcrux_ss = libcrux::kem::kyber768_decapsulate_derand(libcrux_key_pair.private_key(), &libcrux_ct);
   let spec_ss = hacspec_kyber::decapsulate(spec_ct, *spec_key_pair.sk());

   assert_eq!(libcrux_ss, spec_ss);
}

fn modify_ciphertext_pair(libcrux_ct: KyberCiphertext<KYBER768_CIPHERTEXT_SIZE>, mut spec_ct : hacspec_kyber::Ciphertext) -> (KyberCiphertext<KYBER768_CIPHERTEXT_SIZE>, hacspec_kyber::Ciphertext) {
    let mut random_bytes = [0u8; 3];
    OsRng.fill_bytes(&mut random_bytes);

    let mut byte_to_modify_with: u8 = random_bytes[0];
    if byte_to_modify_with == 0 {
        byte_to_modify_with += 1;
    }

    let random_u16 = (random_bytes[2] as usize) << 8 | random_bytes[1] as usize;
    let position = random_u16 % KYBER768_CIPHERTEXT_SIZE;

    let mut raw_libcrux_ct : [u8; KYBER768_CIPHERTEXT_SIZE] = libcrux_ct.into();
    raw_libcrux_ct[position] ^= byte_to_modify_with;

    spec_ct[position] ^= byte_to_modify_with;

    (raw_libcrux_ct.try_into().unwrap(), spec_ct)
}

#[test]
fn implicit_rejection_happens_the_same_way() {
    let mut keygen_seed = [0u8; KYBER768_KEY_GENERATION_SEED_SIZE];
    OsRng.fill_bytes(&mut keygen_seed);

    let libcrux_key_pair = libcrux::kem::kyber768_generate_keypair_derand(keygen_seed).unwrap();
    let spec_key_pair = hacspec_kyber::generate_keypair(keygen_seed).unwrap();

    let mut message = [0u8; KYBER768_SHARED_SECRET_SIZE];
    OsRng.fill_bytes(&mut message);

    let (libcrux_ct, libcrux_ss) = libcrux::kem::kyber768_encapsulate_derand(&libcrux_key_pair.pk().into(), message).unwrap();
    let (spec_ct, spec_ss) = hacspec_kyber::encapsulate(*spec_key_pair.pk(), message).unwrap();

    assert_eq!(libcrux_ct.as_ref(), spec_ct);
    assert_eq!(libcrux_ss.as_ref(), spec_ss);

    let (libcrux_ct, _) = libcrux::kem::kyber768_encapsulate_derand(&libcrux_key_pair.pk().into(), message).unwrap();
    let (spec_ct, _) = hacspec_kyber::encapsulate(*spec_key_pair.pk(), message).unwrap();

    let (modified_libcrux_ct, modified_spec_ct) = modify_ciphertext_pair(libcrux_ct, spec_ct);

   let libcrux_ss = libcrux::kem::kyber768_decapsulate_derand(libcrux_key_pair.private_key(), &modified_libcrux_ct);
   let spec_ss = hacspec_kyber::decapsulate(modified_spec_ct, *spec_key_pair.sk());

   assert_eq!(libcrux_ss, spec_ss);
}
