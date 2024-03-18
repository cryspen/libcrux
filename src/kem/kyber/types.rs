macro_rules! impl_generic_struct {
    ($name:ident) => {
        pub struct $name<const SIZE: usize> {
            pub(super) value: [u8; SIZE],
        }

        impl<const SIZE: usize> AsRef<[u8]> for $name<SIZE> {
            fn as_ref(&self) -> &[u8] {
                &self.value
            }
        }

        impl<const SIZE: usize> From<[u8; SIZE]> for $name<SIZE> {
            fn from(value: [u8; SIZE]) -> Self {
                Self { value }
            }
        }

        impl<const SIZE: usize> From<&[u8; SIZE]> for $name<SIZE> {
            fn from(value: &[u8; SIZE]) -> Self {
                Self {
                    value: value.clone(),
                }
            }
        }

        impl<const SIZE: usize> From<$name<SIZE>> for [u8; SIZE] {
            fn from(value: $name<SIZE>) -> Self {
                value.value
            }
        }

        impl<const SIZE: usize> TryFrom<&[u8]> for $name<SIZE> {
            type Error = core::array::TryFromSliceError;

            fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
                match value.try_into() {
                    Ok(value) => Ok(Self { value }),
                    Err(e) => Err(e),
                }
            }
        }

        impl<const SIZE: usize> $name<SIZE> {
            pub fn as_slice(&self) -> &[u8; SIZE] {
                &self.value
            }

            pub fn split_at(&self, mid: usize) -> (&[u8], &[u8]) {
                self.value.split_at(mid)
            }

            pub const fn len(&self) -> usize {
                SIZE
            }
        }
    };
}
macro_rules! impl_index_impls_for_generic_struct {
    ($name:ident) => {
        impl<const SIZE: usize> core::ops::Index<usize> for $name<SIZE> {
            type Output = u8;

            fn index(&self, index: usize) -> &Self::Output {
                &self.value[index]
            }
        }

        impl<const SIZE: usize> core::ops::Index<core::ops::Range<usize>> for $name<SIZE> {
            type Output = [u8];

            fn index(&self, range: core::ops::Range<usize>) -> &Self::Output {
                &self.value[range]
            }
        }

        impl<const SIZE: usize> core::ops::Index<core::ops::RangeTo<usize>> for $name<SIZE> {
            type Output = [u8];

            fn index(&self, range: core::ops::RangeTo<usize>) -> &Self::Output {
                &self.value[range]
            }
        }

        impl<const SIZE: usize> core::ops::Index<core::ops::RangeFrom<usize>> for $name<SIZE> {
            type Output = [u8];

            fn index(&self, range: core::ops::RangeFrom<usize>) -> &Self::Output {
                &self.value[range]
            }
        }
    };
}

impl_generic_struct!(MlKemCiphertext);
impl_generic_struct!(MlKemPrivateKey);
impl_generic_struct!(MlKemPublicKey);

// These traits are used only in `ind_cpa` for kyber cipher text.
mod index_impls {
    use super::*;
    impl_index_impls_for_generic_struct!(MlKemCiphertext);
    impl_index_impls_for_generic_struct!(MlKemPrivateKey);
    impl_index_impls_for_generic_struct!(MlKemPublicKey);
}

/// An ML-KEM key pair
pub struct MlKemKeyPair<const PRIVATE_KEY_SIZE: usize, const PUBLIC_KEY_SIZE: usize> {
    pub(crate) sk: MlKemPrivateKey<PRIVATE_KEY_SIZE>,
    pub(crate) pk: MlKemPublicKey<PUBLIC_KEY_SIZE>,
}

impl<const PRIVATE_KEY_SIZE: usize, const PUBLIC_KEY_SIZE: usize>
    MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>
{
    /// Creates a new [`MlKemKeyPair`].
    pub fn new(sk: [u8; PRIVATE_KEY_SIZE], pk: [u8; PUBLIC_KEY_SIZE]) -> Self {
        Self {
            sk: sk.into(),
            pk: pk.into(),
        }
    }

    pub fn from(
        sk: MlKemPrivateKey<PRIVATE_KEY_SIZE>,
        pk: MlKemPublicKey<PUBLIC_KEY_SIZE>,
    ) -> Self {
        Self { sk, pk }
    }

    pub fn public_key(&self) -> &MlKemPublicKey<PUBLIC_KEY_SIZE> {
        &self.pk
    }

    pub fn private_key(&self) -> &MlKemPrivateKey<PRIVATE_KEY_SIZE> {
        &self.sk
    }

    pub fn pk(&self) -> &[u8; PUBLIC_KEY_SIZE] {
        self.pk.as_slice()
    }

    pub fn sk(&self) -> &[u8; PRIVATE_KEY_SIZE] {
        self.sk.as_slice()
    }

    #[cfg(feature = "tests")]
    pub fn into_parts(
        self,
    ) -> (
        MlKemPrivateKey<PRIVATE_KEY_SIZE>,
        MlKemPublicKey<PUBLIC_KEY_SIZE>,
    ) {
        (self.sk, self.pk)
    }
}
