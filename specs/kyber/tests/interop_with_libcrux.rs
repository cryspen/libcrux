//! Test spec - code interop

use hacspec_kyber::{KYBER768_KEY_GENERATION_SEED_SIZE, KYBER768_SHARED_SECRET_SIZE};
use rand::{rngs::OsRng, RngCore};

#[test]
fn kyber768_spec_against_libcrux_interop() {
    let mut keygen_seed = [0u8; KYBER768_KEY_GENERATION_SEED_SIZE];
    OsRng.fill_bytes(&mut keygen_seed);

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
