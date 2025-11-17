use serde::Deserialize;

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
pub struct KeyGenPrompt {
    pub tcId: usize,

    #[serde(with = "hex::serde")]
    pub z: [u8; 32],

    #[serde(with = "hex::serde")]
    pub d: [u8; 32],
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
pub struct KeyGenPromptTestGroup {
    pub tgId: usize,
    pub testType: String,
    pub parameterSet: String,
    pub tests: Vec<KeyGenPrompt>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
pub struct Prompts<TG> {
    pub vsId: usize,
    pub algorithm: String,
    pub mode: String,
    pub revision: String,
    pub isSample: bool,
    pub testGroups: Vec<TG>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
pub struct KeyGenResult {
    pub tcId: usize,

    #[serde(with = "hex::serde")]
    pub ek: Vec<u8>,

    #[serde(with = "hex::serde")]
    pub dk: Vec<u8>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
pub struct ResultKeyGenTestGroup {
    pub tgId: usize,
    pub tests: Vec<KeyGenResult>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
pub struct Results<TG> {
    pub vsId: usize,
    pub algorithm: String,
    pub mode: String,
    pub revision: String,
    pub isSample: bool,
    pub testGroups: Vec<TG>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
pub struct EncapPrompt {
    pub tcId: usize,

    #[serde(with = "hex::serde")]
    pub ek: Vec<u8>,

    #[serde(with = "hex::serde")]
    pub m: [u8; 32],
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
pub struct DecapPrompt {
    pub tcId: usize,

    #[serde(with = "hex::serde")]
    pub c: Vec<u8>,
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
pub struct EncapDecapPromptTestGroup {
    pub tgId: usize,
    pub testType: String,
    pub parameterSet: String,
    #[serde(flatten)]
    pub tests: EncapDecapTestPrompts,
}

#[allow(non_snake_case, dead_code)]
#[derive(Deserialize)]
#[serde(tag = "function")]
pub enum EncapDecapTestPrompts {
    #[serde(rename(deserialize = "encapsulation"))]
    EncapTests { tests: Vec<EncapPrompt> },
    #[serde(rename(deserialize = "decapsulation"))]
    DecapTests {
        #[serde(with = "hex::serde")]
        dk: Vec<u8>,
        tests: Vec<DecapPrompt>,
    },
}

#[derive(Deserialize)]
#[serde(untagged)]
#[allow(non_snake_case, dead_code)]
pub enum EncapDecapResult {
    EncapResult {
        tcId: usize,
        #[serde(with = "hex::serde")]
        c: Vec<u8>,
        #[serde(with = "hex::serde")]
        k: Vec<u8>,
    },
    DecapResult {
        tcId: usize,
        #[serde(with = "hex::serde")]
        k: Vec<u8>,
    },
}

#[derive(Deserialize)]
#[allow(non_snake_case, dead_code)]
pub struct ResultEncapDecapTestGroup {
    pub tgId: usize,
    pub tests: Vec<EncapDecapResult>,
}

macro_rules! impl_tests {
    ($ty:ty, $variant:literal) => {
        impl $ty {
            pub fn load() -> Self {
                let prompt_data: &str = include_str!(concat!(
                    "../../acvp/mlkem-1_1_0_35/",
                    $variant,
                    "/prompt.json"
                ));
                let results_data: &str = include_str!(concat!(
                    "../../acvp/mlkem-1_1_0_35/",
                    $variant,
                    "/expectedResults.json"
                ));

                let prompts =
                    serde_json::from_str(prompt_data).expect("Could not deserialize KAT file.");
                let results =
                    serde_json::from_str(results_data).expect("Could not deserialize KAT file.");

                let tests = Self { prompts, results };

                tests
            }
        }
    };
}

pub struct KeyGenTests {
    pub prompts: Prompts<KeyGenPromptTestGroup>,
    pub results: Results<ResultKeyGenTestGroup>,
}

pub struct EncapDecapTests {
    pub prompts: Prompts<EncapDecapPromptTestGroup>,
    pub results: Results<ResultEncapDecapTestGroup>,
}

impl_tests!(KeyGenTests, "keygen");
impl_tests!(EncapDecapTests, "encap-decap");
