mod schema;
pub use schema::*;

pub struct VerifyTest {
    pub schema: VerifySchema,
}

macro_rules! impl_parameter_set {
    ($name:ident, $parameter_set:literal) => {
        impl VerifyTest {
            pub fn $name() -> Self {
                let data: &str = include_str!(concat!(
                    "../../wycheproof/mldsa_",
                    $parameter_set,
                    "_verify_test.json"
                ));
                let schema: VerifySchema =
                    serde_json::from_str(data).expect("Could not deserialize KAT file.");

                Self { schema }
            }
        }
    };
}

impl_parameter_set!(verify_44, 44);
impl_parameter_set!(verify_65, 65);
impl_parameter_set!(verify_87, 87);
