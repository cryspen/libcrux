//! Wycheproof ML-DSA Known Answer Tests
//!
//! The JSON files for ML-DSA were taken from <https://github.com/C2SP/wycheproof>, as of commit [b51abcfb8dafa5316791e57cf48512a2147d9671](https://github.com/C2SP/wycheproof/tree/b51abcfb8dafa5316791e57cf48512a2147d9671)
//!
//! ### Example usage
//! ```rust
//! use libcrux_kats::wycheproof::mldsa::{ParameterSet, MlDsaSignTestsNoSeed};
//!
//! // load the tests for the ML-DSA-44 parameter set
//! let signing_tests = MlDsaSignTestsNoSeed::load(ParameterSet::MlDsa44);
//!
//! for test_group in signing_tests.test_groups {
//!     for test in test_group.tests {
//!         // ...
//!     }
//! }
//! ```

pub mod sign_noseed_schema;

pub mod verify_schema;

pub use sign_noseed_schema::MlDsaSignTestsNoSeed;
pub use verify_schema::MlDsaVerifyTests;

/// Parameter sets for ML-DSA
pub enum ParameterSet {
    MlDsa44,
    MlDsa65,
    MlDsa87,
}

macro_rules! impl_sign_noseed {
    ($name:ident, $parameter_set:literal) => {
        impl MlDsaSignTestsNoSeed {
            fn $name() -> Self {
                let data: &str = include_str!(concat!(
                    "../../wycheproof/mldsa_",
                    $parameter_set,
                    "_sign_noseed_test.json"
                ));
                serde_json::from_str(data).expect("Could not deserialize KAT file.")
            }
        }
    };
}

impl_sign_noseed!(sign_44, 44);
impl_sign_noseed!(sign_65, 65);
impl_sign_noseed!(sign_87, 87);

macro_rules! impl_verify {
    ($name:ident, $parameter_set:literal) => {
        impl MlDsaVerifyTests {
            fn $name() -> Self {
                let data: &str = include_str!(concat!(
                    "../../wycheproof/mldsa_",
                    $parameter_set,
                    "_verify_test.json"
                ));
                serde_json::from_str(data).expect("Could not deserialize KAT file.")
            }
        }
    };
}

impl_verify!(verify_44, 44);
impl_verify!(verify_65, 65);
impl_verify!(verify_87, 87);

impl MlDsaSignTestsNoSeed {
    /// Load the [`MlDsaSignTests`] for the given [`ParameterSet`].
    pub fn load(parameter_set: ParameterSet) -> Self {
        match parameter_set {
            ParameterSet::MlDsa44 => Self::sign_44(),
            ParameterSet::MlDsa65 => Self::sign_65(),
            ParameterSet::MlDsa87 => Self::sign_87(),
        }
    }
}
impl MlDsaVerifyTests {
    /// Load the [`MlDsaVerifyTests`] for the given [`ParameterSet`].
    pub fn load(parameter_set: ParameterSet) -> Self {
        match parameter_set {
            ParameterSet::MlDsa44 => Self::verify_44(),
            ParameterSet::MlDsa65 => Self::verify_65(),
            ParameterSet::MlDsa87 => Self::verify_87(),
        }
    }
}
