mod schema;
pub use schema::*;

pub struct MlDsaSignTest {
    pub schema: MlDsaSignSchema,
}

macro_rules! impl_parameter_set {
    ($name:ident, $parameter_set:literal) => {
        impl MlDsaSignTest {
            pub fn $name() -> Self {
                let data: &str = include_str!(concat!(
                    "../../wycheproof/mldsa_",
                    $parameter_set,
                    "_sign_noseed_test.json"
                ));
                let schema = serde_json::from_str(data).expect("Could not deserialize KAT file.");

                Self { schema }
            }
        }
    };
}

impl_parameter_set!(sign_44, 44);
impl_parameter_set!(sign_65, 65);
impl_parameter_set!(sign_87, 87);
