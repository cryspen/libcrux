macro_rules! impl_generic_struct {
    ($name:ident) => {
        pub struct $name<const SIZE: usize> {
            value: [u8; SIZE],
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

        impl<const SIZE: usize> From<$name<SIZE>> for [u8; SIZE] {
            fn from(value: $name<SIZE>) -> Self {
                value.value
            }
        }

        impl<const SIZE: usize> TryFrom<&[u8]> for $name<SIZE> {
            type Error = core::array::TryFromSliceError;

            fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
                Ok(Self {
                    value: value.try_into()?,
                })
            }
        }

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
