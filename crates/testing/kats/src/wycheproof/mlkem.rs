//! Wycheproof ML-KEM Known Answer Tests
//!
//! The JSON file for ML-KEM was taken from <https://github.com/C2SP/wycheproof>, as of commit [b51abcfb8dafa5316791e57cf48512a2147d9671](https://github.com/C2SP/wycheproof/tree/b51abcfb8dafa5316791e57cf48512a2147d9671)
//!
//! ### Example usage
//! ```rust
//! use libcrux_kats::wycheproof::mlkem::{ParameterSet, MlKemTests};
//!
//! // load the tests for the ML-KEM-512 parameter set
//! let tests = MlKemTests::load();
//!
//! for test_group in tests.keygen_and_decaps_tests(ParameterSet::MlKem512) {
//!     for test in &test_group.tests {
//!         // ...
//!     }
//! }
//! ```

pub mod schema;

pub use schema::*;

impl schema::MlKemTests {
    pub fn load() -> Self {
        let data: &str = include_str!("../../wycheproof/mlkem_test.json");
        serde_json::from_str(data).expect("Could not deserialize KAT file.")
    }

    pub fn keygen_and_decaps_tests(
        &self,
        parameter_set: ParameterSet,
    ) -> impl Iterator<Item = &MlKemTestGroup> {
        self.test_groups
            .iter()
            .filter_map(|g| {
                if let TestGroup::MlKemTestGroup(g) = g {
                    Some(g)
                } else {
                    None
                }
            })
            .filter(move |g| g.parameter_set == parameter_set)
    }
    pub fn encaps_tests(
        &self,
        parameter_set: ParameterSet,
    ) -> impl Iterator<Item = &MlKemEncapsTestGroup> {
        self.test_groups
            .iter()
            .filter_map(|g| {
                if let TestGroup::MlKemEncapsTestGroup(g) = g {
                    Some(g)
                } else {
                    None
                }
            })
            .filter(move |g| g.parameter_set == parameter_set)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    // test that data is loaded successfully
    #[test]
    fn test_load() {
        MlKemTests::load();
    }
}
