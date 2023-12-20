use libcrux::{digest::incremental::IncrementalShake128, digest::shake128, kem};

#[test]
fn kyber_768_10000_kats() {
    let mut xof = IncrementalShake128::new();
    xof.absorb(&[1, 2, 3, 4, 5]);
    let xof_bytes = xof.squeeze_nblocks::<64>();

    println!("{:?}", xof_bytes);
}
