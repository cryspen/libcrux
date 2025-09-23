pub mod schema;

pub use schema::*;

impl schema::MlKemTests {
    pub fn load() -> Self {
        let data: &str = include_str!("../../wycheproof/mlkem_test.json");
        serde_json::from_str(data).expect("Could not deserialize KAT file.")
    }

    pub fn keygen_and_decaps_tests(
        &self,
        parameter_set: MlKemParameterSet,
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
        parameter_set: MlKemParameterSet,
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
