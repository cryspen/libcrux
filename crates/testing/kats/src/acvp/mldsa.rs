//! ACVP ML-DSA Known Answer Tests
//!
//! The JSON files for ML-DSA were taken from <https://github.com/usnistgov/ACVP-Server>, as of
//! commit [112690e8484dba7077709a05b1f3af58ddefdd5d](https://github.com/usnistgov/ACVP-Server/commit/112690e8484dba7077709a05b1f3af58ddefdd5d).
//!
//! ### Example usage
//! ```rust
//! use libcrux_kats::acvp::mldsa::{KeyGenTests, SigGenTests, SigVerTests};
//!
//! // keygen tests
//! let keygen_tests = KeyGenTests::load();
//!
//! for test_group in keygen_tests.prompts.testGroups {
//!    for test in test_group.tests {
//!        // retrieve the expected result for that test
//!         let expected_result
//!             = keygen_tests.results.find_expected_result(test_group.tgId, test.tcId);
//!    }
//! }
//!
//! // siggen tests
//! let siggen_tests = SigGenTests::load();
//!
//! for test_group in siggen_tests.prompts.testGroups {
//!    for test in test_group.tests {
//!        // retrieve the expected result for that test
//!         let expected_result
//!             = siggen_tests.results.find_expected_result(test_group.tgId, test.tcId);
//!    }
//! }
//!
//! // sigver tests
//! let sigver_tests = SigVerTests::load();
//!
//! for test_group in sigver_tests.prompts.testGroups {
//!    for test in test_group.tests {
//!        // retrieve the expected result for that test
//!         let expected_result
//!             = sigver_tests.results.find_expected_result(test_group.tgId, test.tcId);
//!    }
//! }
//! ```
pub mod common;
pub mod keygen_schema;
pub mod sign_schema;
pub mod verify_schema;

macro_rules! impl_tests {
    ($ty:ty, $variant:literal) => {
        impl $ty {
            pub fn load() -> Self {
                let prompt_data: &str = include_str!(concat!(
                    "../../acvp/mldsa-1_1_0_40/",
                    $variant,
                    "/prompt.json"
                ));
                let results_data: &str = include_str!(concat!(
                    "../../acvp/mldsa-1_1_0_40/",
                    $variant,
                    "/expectedResults.json"
                ));

                let prompts =
                    serde_json::from_str(prompt_data).expect("Could not deserialize KAT file.");
                let results =
                    serde_json::from_str(results_data).expect("Could not deserialize KAT file.");

                let tests = Self { prompts, results };

                // checks
                assert!(tests.prompts.algorithm == "ML-DSA");
                assert!(tests.prompts.revision == "FIPS204");
                assert!(tests.results.algorithm == "ML-DSA");
                assert!(tests.results.revision == "FIPS204");

                tests
            }
        }
    };
}

pub struct KeyGenTests {
    pub prompts: common::Prompts<keygen_schema::KeyGenPromptTestGroup>,
    pub results: common::Results<keygen_schema::ResultKeyGenTestGroup>,
}

pub struct SigGenTests {
    pub prompts: common::Prompts<sign_schema::SigGenPromptTestGroup>,
    pub results: common::Results<sign_schema::ResultSigGenTestGroup>,
}
pub struct SigVerTests {
    pub prompts: common::Prompts<verify_schema::SigVerPromptTestGroup>,
    pub results: common::Results<verify_schema::ResultSigVerTestGroup>,
}

impl_tests!(KeyGenTests, "keygen");
impl_tests!(SigGenTests, "siggen");
impl_tests!(SigVerTests, "sigver");
