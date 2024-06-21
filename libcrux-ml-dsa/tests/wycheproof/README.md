The JSON files were taken from `https://github.com/C2SP/wycheproof/pull/112`, and

`sign_schema.rs` was was generated with [quicktype](https://github.com/glideapps/quicktype),
using the commands:

```
cat mldsa_44_draft_sign_test.json | quicktype -o sign_schema.rust
mv sign_schema.rust sign_schema.rs
```

`verify_schema.rs` was generated using:

```
cat mldsa_44_draft_verify_test.json | quicktype -o verify_schema.rust
mv verify_schema.rust verify_schema.rs
```
