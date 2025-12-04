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
pub mod keygen_schema;
pub mod sign_schema;
pub mod verify_schema;

pub struct KeyGenTests {
    pub prompts: super::schema_common::Prompts<keygen_schema::KeyGenPromptTestGroup>,
    pub results: super::schema_common::Results<keygen_schema::ResultKeyGenTestGroup>,
}

pub struct SigGenTests {
    pub prompts: super::schema_common::Prompts<sign_schema::SigGenPromptTestGroup>,
    pub results: super::schema_common::Results<sign_schema::ResultSigGenTestGroup>,
}
pub struct SigVerTests {
    pub prompts: super::schema_common::Prompts<verify_schema::SigVerPromptTestGroup>,
    pub results: super::schema_common::Results<verify_schema::ResultSigVerTestGroup>,
}

super::impl_tests!(KeyGenTests, "mldsa-1_1_0_40", "keygen");
super::impl_tests!(SigGenTests, "mldsa-1_1_0_40", "siggen");
super::impl_tests!(SigVerTests, "mldsa-1_1_0_40", "sigver");
