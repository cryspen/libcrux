pub struct Blake2b;
pub struct Blake2s;

pub enum Error {
    MaximumLengthExceeded,
    InvalidChunkLength,
    Unexpected,
}

impl Error {
    fn from_sized_update_error(err: libcrux_blake2::Error) -> Self {
        match err {
            libcrux_blake2::Error::MaximumLengthExceeded => Self::MaximumLengthExceeded,
            libcrux_blake2::Error::InvalidChunkLength => Self::InvalidChunkLength,
            _ => Self::Unexpected,
        }
    }
}

impl<'a, const KEY_LEN: usize, const OUT_LEN: usize>
    super::Prf<&'a mut [u8; OUT_LEN], &'a [u8; KEY_LEN], &'a [u8]> for Blake2b
where
    Blake2bKey: SupportsLen<KEY_LEN>,
    Blake2bOut: SupportsLen<OUT_LEN>,
{
    type Error = Error;

    fn eval(
        out: &'a mut [u8; OUT_LEN],
        k: &'a [u8; KEY_LEN],
        msg: &'a [u8],
    ) -> Result<(), Self::Error> {
        let mut hasher = libcrux_blake2::Blake2bBuilder::new_keyed_const(k)
            .unwrap()
            .build_const_digest_len()
            .unwrap();
        hasher.update(msg).map_err(Error::from_sized_update_error)?;
        hasher.finalize(out);
        Ok(())
    }
}

impl<'a, const KEY_LEN: usize, const OUT_LEN: usize>
    super::Prf<&'a mut [u8; OUT_LEN], &'a [u8; KEY_LEN], &'a [u8]> for Blake2s
where
    Blake2sKey: SupportsLen<KEY_LEN>,
    Blake2sOut: SupportsLen<OUT_LEN>,
{
    type Error = Error;

    fn eval(
        out: &'a mut [u8; OUT_LEN],
        k: &'a [u8; KEY_LEN],
        msg: &'a [u8],
    ) -> Result<(), Self::Error> {
        let mut hasher = libcrux_blake2::Blake2sBuilder::new_keyed_const(k)
            .unwrap()
            .build_const_digest_len()
            .unwrap();
        hasher.update(msg).map_err(Error::from_sized_update_error)?;
        hasher.finalize(out);
        Ok(())
    }
}

struct Blake2bOut;
struct Blake2bKey;
struct Blake2sOut;
struct Blake2sKey;

trait SupportsLen<const N: usize> {}

macro_rules! impl_supports_len {
    ($ty:ty, $($len:expr),*) => {
        $( impl SupportsLen<$len> for $ty {} )*
    };
}

#[rustfmt::skip]
impl_supports_len!(Blake2sOut,       1,  2,  3,  4,  5,  6,  7,  8,  9,
                                10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
                                20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
                                30, 31, 32);

#[rustfmt::skip]
impl_supports_len!(Blake2sKey,       1,  2,  3,  4,  5,  6,  7,  8,  9,
                                10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
                                20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
                                30, 31, 32);

#[rustfmt::skip]
impl_supports_len!(Blake2bOut,       1,  2,  3,  4,  5,  6,  7,  8,  9,
                                10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
                                20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
                                30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
                                40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
                                50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
                                60, 61, 62, 63, 64);

#[rustfmt::skip]
impl_supports_len!(Blake2bKey,       1,  2,  3,  4,  5,  6,  7,  8,  9,
                                10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
                                20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
                                30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
                                40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
                                50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
                                60, 61, 62, 63, 64);

