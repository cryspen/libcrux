pub mod schema;

pub use schema::*;

impl schema::MlkemTest {
    pub fn load() -> Self {
        let data: &str = include_str!("../../wycheproof/mlkem_test.json");
        serde_json::from_str(data).expect("Could not deserialize KAT file.")
    }
}

#[cfg(test)]
mod test {
    use super::*;

    // test that data is loaded successfully
    #[test]
    fn test_load() {
        MlkemTest::load();
    }
}
