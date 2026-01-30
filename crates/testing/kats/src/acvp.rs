//! ACVP Known Answer Tests

#[cfg(feature = "mldsa")]
pub mod mldsa;

#[cfg(feature = "mlkem")]
pub mod mlkem;

pub mod schema_common;

#[cfg(any(feature = "mldsa", feature = "mlkem"))]
/// Shared macro for implementing loading of KATs
macro_rules! impl_tests {
    ($ty:ty, $directory:literal, $variant:literal) => {
        impl $ty {
            pub fn load() -> Self {
                let prompt_data: &str = include_str!(concat!(
                    "../../acvp/",
                    $directory,
                    "/",
                    $variant,
                    "/prompt.json"
                ));
                let results_data: &str = include_str!(concat!(
                    "../../acvp/",
                    $directory,
                    "/",
                    $variant,
                    "/expectedResults.json"
                ));

                let prompts =
                    serde_json::from_str(prompt_data).expect("Could not deserialize KAT file.");
                let results =
                    serde_json::from_str(results_data).expect("Could not deserialize KAT file.");

                Self { prompts, results }
            }
        }
    };
}

#[cfg(any(feature = "mldsa", feature = "mlkem"))]
pub(super) use impl_tests;
