pub mod sign_schema;
use sign_schema::*;

pub mod verify_schema;
use verify_schema::*;

pub struct MlDsaSignTest {
    pub schema: MlDsaSignSchema,
}

macro_rules! impl_sign_noseed {
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

impl_sign_noseed!(sign_44, 44);
impl_sign_noseed!(sign_65, 65);
impl_sign_noseed!(sign_87, 87);

pub struct MlDsaVerifyTest {
    pub schema: MlDsaVerifySchema,
}

macro_rules! impl_verify {
    ($name:ident, $parameter_set:literal) => {
        impl MlDsaVerifyTest {
            pub fn $name() -> Self {
                let data: &str = include_str!(concat!(
                    "../../wycheproof/mldsa_",
                    $parameter_set,
                    "_verify_test.json"
                ));
                let schema = serde_json::from_str(data).expect("Could not deserialize KAT file.");

                Self { schema }
            }
        }
    };
}

impl_verify!(verify_44, 44);
impl_verify!(verify_65, 65);
impl_verify!(verify_87, 87);
