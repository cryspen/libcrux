use std::marker::PhantomData;

pub struct Sha2_256;
pub struct Sha2_384;
pub struct Sha2_512;

pub enum Sha2Dynamic {
    Sha256,
    Sha384,
    Sha512,
}

pub enum FixedExtractError {
    ArgumentTooLong,
    Unknown,
}

pub enum ExtractError {
    PrkTooShort,
    ArgumentTooLong,
    Unknown,
}

pub enum FixedExpandError {
    OutputTooLong,
    ArgumentTooLong,
    Unknown,
}

pub enum ExpandError {
    OutputTooLong,
    PrkTooShort,
    ArgumentTooLong,
    Unknown,
}

pub struct Hkdf<Algo>(PhantomData<Algo>);

impl Hkdf<Sha2Dynamic> {
    pub fn extract(
        algo: Sha2Dynamic,
        prk: &mut [u8],
        salt: &[u8],
        ikm: &[u8],
    ) -> Result<(), ExtractError> {
        match algo {
            Sha2Dynamic::Sha256 => Hkdf::<Sha2_256>::extract(prk, salt, ikm),
            Sha2Dynamic::Sha384 => Hkdf::<Sha2_384>::extract(prk, salt, ikm),
            Sha2Dynamic::Sha512 => Hkdf::<Sha2_512>::extract(prk, salt, ikm),
        }
    }

    pub fn expand(
        algo: Sha2Dynamic,
        okm: &mut [u8],
        prk: &[u8],
        info: &[u8],
    ) -> Result<(), ExpandError> {
        match algo {
            Sha2Dynamic::Sha256 => Hkdf::<Sha2_256>::expand(okm, prk, info),
            Sha2Dynamic::Sha384 => Hkdf::<Sha2_384>::expand(okm, prk, info),
            Sha2Dynamic::Sha512 => Hkdf::<Sha2_512>::expand(okm, prk, info),
        }
    }
}

macro_rules! impl_concrete {
    ($hash:ty, $len:expr, $impl_mod:path) => {
        impl Hkdf<$hash> {
            pub fn extract_fixed(
                prk: &mut [u8; $len],
                salt: &[u8],
                ikm: &[u8],
            ) -> Result<(), FixedExtractError> {
                #[rustfmt::skip]
                        use $impl_mod::{extract};
                extract(prk, salt, ikm).map_err(FixedExtractError::from_hkdf_error)
            }

            pub fn expand_fixed(
                okm: &mut [u8],
                prk: &[u8; $len],
                info: &[u8],
            ) -> Result<(), FixedExpandError> {
                #[rustfmt::skip]
                        use $impl_mod::{expand_slice};
                expand_slice(okm, prk, info).map_err(FixedExpandError::from_hkdf_error)
            }

            pub fn extract(prk: &mut [u8], salt: &[u8], ikm: &[u8]) -> Result<(), ExtractError> {
                let (prk, _) = prk
                    .split_at_mut_checked($len)
                    .ok_or(ExtractError::PrkTooShort)?;
                let prk: &mut [u8; $len] = prk.try_into().map_err(|_| ExtractError::Unknown)?;

                Self::extract_fixed(prk, salt, ikm).map_err(ExtractError::from)
            }

            pub fn expand(okm: &mut [u8], prk: &[u8], info: &[u8]) -> Result<(), ExpandError> {
                let (prk, _) = prk.split_at_checked($len).ok_or(ExpandError::PrkTooShort)?;
                let prk: &[u8; $len] = prk.try_into().map_err(|_| ExpandError::Unknown)?;

                Self::expand_fixed(okm, prk, info).map_err(ExpandError::from)
            }
        }
    };
}

impl_concrete!(Sha2_256, 32, libcrux_hkdf::sha2_256);
impl_concrete!(Sha2_384, 48, libcrux_hkdf::sha2_384);
impl_concrete!(Sha2_512, 64, libcrux_hkdf::sha2_512);

impl From<FixedExtractError> for ExtractError {
    fn from(value: FixedExtractError) -> Self {
        match value {
            FixedExtractError::ArgumentTooLong => Self::ArgumentTooLong,
            FixedExtractError::Unknown => Self::Unknown,
        }
    }
}

impl From<FixedExpandError> for ExpandError {
    fn from(value: FixedExpandError) -> Self {
        match value {
            FixedExpandError::ArgumentTooLong => Self::ArgumentTooLong,
            FixedExpandError::Unknown => Self::Unknown,
            FixedExpandError::OutputTooLong => Self::OutputTooLong,
        }
    }
}

impl FixedExtractError {
    fn from_hkdf_error(value: libcrux_hkdf::Error) -> Self {
        match value {
            libcrux_hkdf::Error::OkmTooLarge => Self::Unknown,
            libcrux_hkdf::Error::ArgumentsTooLarge => Self::ArgumentTooLong,
        }
    }
}

impl FixedExpandError {
    fn from_hkdf_error(value: libcrux_hkdf::Error) -> Self {
        match value {
            libcrux_hkdf::Error::OkmTooLarge => Self::OutputTooLong,
            libcrux_hkdf::Error::ArgumentsTooLarge => Self::ArgumentTooLong,
        }
    }
}
