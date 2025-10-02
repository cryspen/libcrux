//! Wycheproof ML-KEM Known Answer Tests
//!
//! The JSON file for ML-KEM was taken from <https://github.com/C2SP/wycheproof>, as of commit [cd136e97040de0842c3a198670b1c5e4f423c940](https://github.com/C2SP/wycheproof/tree/cd136e97040de0842c3a198670b1c5e4f423c940)
//!
//! ### Example usage
//! ```rust
//! use libcrux_kats::wycheproof::mlkem::{ParameterSet, MlKemTests};
//!
//! // load the tests for the ML-KEM-512 parameter set
//! let tests = MlKemTests::load(ParameterSet::MlKem512);
//!
//! for test_group in tests.keygen_and_decaps_tests() {
//!     for test in &test_group.tests {
//!         // ...
//!     }
//! }
//! ```

pub mod schema;

pub use schema::*;

macro_rules! impl_tests {
    ($name:ident, $parameter_set:literal) => {
        impl MlKemTests {
            fn $name() -> Self {
                let data: &str = include_str!(concat!(
                    "../../wycheproof/mlkem_",
                    $parameter_set,
                    "_test.json"
                ));
                serde_json::from_str(data).expect("Could not deserialize KAT file.")
            }
        }
    };
}
impl_tests!(mlkem_512, 512);
impl_tests!(mlkem_768, 768);
impl_tests!(mlkem_1024, 1024);

impl schema::MlKemTests {
    pub fn load(parameter_set: ParameterSet) -> Self {
        match parameter_set {
            ParameterSet::MlKem512 => Self::mlkem_512(),
            ParameterSet::MlKem768 => Self::mlkem_768(),
            ParameterSet::MlKem1024 => Self::mlkem_1024(),
        }
    }
    pub fn keygen_and_decaps_tests(&self) -> impl Iterator<Item = &MlKemTestGroup> {
        self.test_groups.iter().filter_map(|g| {
            if let TestGroup::MlKemTestGroup(g) = g {
                Some(g)
            } else {
                None
            }
        })
    }
    pub fn encaps_tests(&self) -> impl Iterator<Item = &MlKemEncapsTestGroup> {
        self.test_groups.iter().filter_map(|g| {
            if let TestGroup::MlKemEncapsTestGroup(g) = g {
                Some(g)
            } else {
                None
            }
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;

    // test that data is loaded successfully
    #[test]
    fn test_load() {
        MlKemTests::load(ParameterSet::MlKem512);
        MlKemTests::load(ParameterSet::MlKem768);
        MlKemTests::load(ParameterSet::MlKem1024);
    }
}
