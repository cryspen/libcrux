pub mod encap_decap_schema;
pub mod keygen_schema;

pub struct KeyGenTests {
    pub prompts: super::schema_common::Prompts<keygen_schema::KeyGenPromptTestGroup>,
    pub results: super::schema_common::Results<keygen_schema::ResultKeyGenTestGroup>,
}

pub struct EncapDecapTests {
    pub prompts: super::schema_common::Prompts<encap_decap_schema::EncapDecapPromptTestGroup>,
    pub results: super::schema_common::Results<encap_decap_schema::ResultEncapDecapTestGroup>,
}

super::impl_tests!(KeyGenTests, "mlkem-1_1_0_35", "keygen");
super::impl_tests!(EncapDecapTests, "mlkem-1_1_0_35", "encap-decap");
