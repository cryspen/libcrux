use super::*;

/// Implementation of Curve25519 backed by Hacl.
pub struct HaclCurve25519;

impl Curve25519 for HaclCurve25519 {
    // The hacl::ecdh function requires all parameters to be 32 byte long, which we enforce using
    // types.
    #[inline(always)]
    fn secret_to_public(pk: &mut [u8; PK_LEN], sk: &[u8; SK_LEN]) {
        secret_to_public(pk, sk)
    }

    // The hacl::ecdh function requires all parameters to be 32 byte long, which we enforce using
    // types.
    #[inline(always)]
    fn ecdh(out: &mut [u8; SHK_LEN], pk: &[u8; PK_LEN], sk: &[u8; SK_LEN]) -> Result<(), Error> {
        ecdh(out, pk, sk)
    }
}

pub fn ecdh_x4(
    out: &mut [[u8; SHK_LEN]; 4],
    pk: &[&[u8; PK_LEN]],
    sk: &[&[u8; SK_LEN]],
) -> Result<(), Error> {
    let mut out1 = [0u8; SHK_LEN];
    let mut out2 = [0u8; SHK_LEN];
    let mut out3 = [0u8; SHK_LEN];
    let mut out4 = [0u8; SHK_LEN];

    let handle1 = {
        let pk_i = pk[0].clone();
        let sk_i = sk[0].clone();

        std::thread::spawn(move || {
            ecdh(&mut out1, &pk_i, &sk_i).unwrap();
        })
    };
    let handle2 = {
        let pk_i = pk[1].clone();
        let sk_i = sk[1].clone();

        std::thread::spawn(move || {
            ecdh(&mut out2, &pk_i, &sk_i).unwrap();
        })
    };
    let handle3 = {
        let pk_i = pk[2].clone();
        let sk_i = sk[2].clone();

        std::thread::spawn(move || {
            ecdh(&mut out3, &pk_i, &sk_i).unwrap();
        })
    };
    let handle4 = {
        let pk_i = pk[3].clone();
        let sk_i = sk[3].clone();

        std::thread::spawn(move || {
            ecdh(&mut out4, &pk_i, &sk_i).unwrap();
        })
    };

    handle1.join().unwrap();
    handle2.join().unwrap();
    handle3.join().unwrap();
    handle4.join().unwrap();

    out[0].copy_from_slice(&out1);
    out[1].copy_from_slice(&out2);
    out[2].copy_from_slice(&out3);
    out[3].copy_from_slice(&out4);

    Ok(())
}

// The hacl::ecdh function requires all parameters to be 32 byte long, which we enforce using
// types.
#[inline(always)]
pub fn secret_to_public(pk: &mut [u8; PK_LEN], sk: &[u8; SK_LEN]) {
    crate::hacl::secret_to_public(pk, sk)
}

// The hacl::ecdh function requires all parameters to be 32 byte long, which we enforce using
// types.
#[inline(always)]
pub fn ecdh(out: &mut [u8; SHK_LEN], pk: &[u8; PK_LEN], sk: &[u8; SK_LEN]) -> Result<(), Error> {
    match crate::hacl::ecdh(out, sk, pk) {
        true => Ok(()),
        false => Err(Error),
    }
}
