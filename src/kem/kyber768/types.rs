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
