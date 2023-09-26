macro_rules! impl_types {
    ($name:ident, $len:expr) => {
        pub struct $name {
            value: [u8; $len],
        }

        impl AsRef<[u8]> for $name {
            fn as_ref(&self) -> &[u8] {
                &self.value
            }
        }

        impl From<[u8; $len]> for $name {
            fn from(value: [u8; $len]) -> Self {
                Self { value }
            }
        }
    };
}

macro_rules! impl_generic_struct {
    ($name:ident) => {
        pub struct $name<const SIZE: usize> {
            key: [u8; SIZE],
        }

        impl<const SIZE: usize> AsRef<[u8]> for $name<SIZE> {
            fn as_ref(&self) -> &[u8] {
                &self.key
            }
        }

        impl<const SIZE: usize> From<[u8; SIZE]> for $name<SIZE> {
            fn from(key: [u8; SIZE]) -> Self {
                Self { key }
            }
        }

        impl<const SIZE: usize> $name<SIZE> {
            pub fn as_slice(&self) -> &[u8; SIZE] {
                &self.key
            }
        }
    };
}
