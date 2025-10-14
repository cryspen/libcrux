pub mod common;
pub mod keygen_schema;
pub mod sign_schema;
pub mod verify_schema;

macro_rules! impl_tests {
    ($ty:ty, $variant:literal) => {
        impl $ty {
            pub fn load() -> Self {
                let prompt_data: &str =
                    include_str!(concat!("../../acvp-1_1_0_40/", $variant, "/prompt.json"));
                let results_data: &str = include_str!(concat!(
                    "../../acvp-1_1_0_40/",
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
