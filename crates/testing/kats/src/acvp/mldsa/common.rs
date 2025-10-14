use serde::Deserialize;
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
pub struct TestGroupResults<R> {
    pub tgId: usize,
    pub tests: Vec<R>,
}

pub trait TestResult {
    fn tc_id(&self) -> usize;
}

impl<T: TestResult> Results<TestGroupResults<T>> {
    #[allow(non_snake_case)]
    pub fn find_expected_result(&self, tgId: usize, tcId: usize) -> &T {
        self.testGroups
            .iter()
            .find(|tg| tg.tgId == tgId)
            .unwrap()
            .tests
            .iter()
            .find(|t| t.tc_id() == tcId)
            .unwrap()
    }
}
