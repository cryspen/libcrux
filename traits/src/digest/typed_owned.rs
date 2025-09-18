#[repr(transparent)]
pub struct Digest<Algo: Hash>(Algo::Digest);

#[repr(transparent)]
pub struct Hasher<Algo: DigestIncremental>(Algo::Hasher);

pub trait Hash: Sized + super::consts::HashConsts {
    type Digest;

    fn hash(digest: &mut Digest<Self>, payload: &[u8]) -> Result<(), super::arrayref::HashError>;
}

pub trait DigestIncremental: Sized + super::consts::HashConsts {
    type Digest;
    type Hasher;
    fn hasher() -> Result<Hasher<Self>, super::InitializeError>;
}

#[macro_export]
macro_rules! impl_hash_typed_owned {
    // literal arm
    ($ty: ty, $digest_len:expr) => {
        impl $crate::digest::typed_owned::Hash for $ty {
            type Digest = [u8; $digest_len];
            fn hash(
                digest: &mut $crate::digest::typed_owned::Digest<Self>,
                payload: &[u8],
            ) -> Result<(), $crate::digest::arrayref::HashError> {
                <$ty as $crate::digest::arrayref::Hash<$digest_len>>::hash(digest.as_mut(), payload)
            }
        }
    };
    // const generic arm
    ($ty: ty, $digest_len:ident, generic) => {
        impl<const $digest_len: usize> $crate::digest::typed_owned::Hash for $ty {
            type Digest = [u8; $digest_len];
            fn hash(
                digest: &mut $crate::digest::typed_owned::Digest<Self>,
                payload: &[u8],
            ) -> Result<(), $crate::digest::arrayref::HashError> {
                <$ty as $crate::digest::arrayref::Hash<$digest_len>>::hash(digest.as_mut(), payload)
            }
        }
    };
}
pub use impl_hash_typed_owned;

#[macro_export]
macro_rules! impl_digest_incremental_typed_owned {
    // literal arm
    ($ty: ty, $digest_len:expr) => {
        impl $crate::digest::typed_owned::DigestIncremental for $ty {
            type Digest = [u8; $digest_len];
            type Hasher = $crate::digest::Hasher<$digest_len, Self>;
            fn hasher(
            ) -> Result<$crate::digest::typed_owned::Hasher<Self>, $crate::digest::InitializeError>
            {
                Self::Hasher::new()
            }
        }
    };
    // const generic arm
    ($ty: ty, $digest_len:ident, generic) => {
        impl<const $digest_len: usize> $crate::digest::typed_owned::DigestIncremental for $ty {
            type Digest = [u8; $digest_len];
            type Hasher = $crate::digest::Hasher<$digest_len, Self>;
            fn hasher(
            ) -> Result<$crate::digest::typed_owned::Hasher<Self>, $crate::digest::InitializeError>
            {
                Self::Hasher::new().map(|hasher| hasher.into())
            }
        }
    };
}
pub use impl_digest_incremental_typed_owned;

impl<Algo: Hash> AsMut<Algo::Digest> for Digest<Algo> {
    fn as_mut(&mut self) -> &mut Algo::Digest {
        &mut self.0
    }
}

impl<const N: usize, Algo: Hash<Digest = [u8; N]>> From<&mut [u8; N]> for &mut Digest<Algo> {
    fn from(bytes: &mut Algo::Digest) -> Self {
        unsafe { core::mem::transmute(bytes) }
    }
}

// hasher conversion
impl<
        const N: usize,
        Algo: DigestIncremental<Digest = [u8; N], Hasher = super::Hasher<N, Algo>>
            + super::DigestIncrementalBase,
    > From<super::Hasher<N, Algo>> for Hasher<Algo>
{
    fn from(hasher: super::Hasher<N, Algo>) -> Self {
        Self(hasher)
    }
}
