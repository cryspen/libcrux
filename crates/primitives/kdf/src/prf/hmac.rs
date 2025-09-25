use std::marker::PhantomData;

struct Sha2_256;
struct Sha2_384;
struct Sha2_512;

struct Hmac<T>(PhantomData<T>);

pub enum FixedError {
    // TODO: Make hmac in libcrux-hmac fallibe
}

pub enum Error {
    OutTooShort,
    // TODO: Make hmac in libcrux-hmac fallibe
}

macro_rules! impl_prf {
    ($hash:ty, $out_len:expr, $hmac:path) => {
        impl<'a> super::Prf<&'a mut [u8; $out_len], &'a [u8], &'a [u8]> for Hmac<$hash> {
            type Error = FixedError;

            fn eval(out: &mut [u8; $out_len], k: &[u8], msg: &[u8]) -> Result<(), Self::Error> {
                $hmac(out, k, msg);
                Ok(())
            }
        }

        impl<'a> super::Prf<&'a mut [u8], &'a [u8], &'a [u8]> for Hmac<$hash> {
            type Error = Error;

            fn eval(out: &mut [u8], k: &[u8], msg: &[u8]) -> Result<(), Self::Error> {
                let out: &mut [u8; $out_len] = out
                    .split_at_mut_checked($out_len)
                    .ok_or(Error::OutTooShort)?
                    .0
                    .try_into()
                    .unwrap();
                $hmac(out, k, msg);
                Ok(())
            }
        }
    };
}

impl_prf!(Sha2_256, 32, libcrux_hmac::hmac_sha2_256);
impl_prf!(Sha2_384, 48, libcrux_hmac::hmac_sha2_384);
impl_prf!(Sha2_512, 64, libcrux_hmac::hmac_sha2_512);

impl From<FixedError> for Error {
    fn from(value: FixedError) -> Self {
        match value {}
    }
}
