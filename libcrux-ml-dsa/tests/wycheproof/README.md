The JSON files were taken from `https://github.com/C2SP/wycheproof/pull/112`.

Both `sign_schema.rs` and `verify_schema.rs` were generated with
[quicktype](https://github.com/glideapps/quicktype), using the commands:

```
cat mldsa_44_draft_sign_test.json | quicktype --derive-partial-eq -o sign_schema.rust
mv sign_schema.rust sign_schema.rs
```

for `sign_schema.rs` and:

```
cat mldsa_44_draft_verify_test.json | quicktype --derive-partial-eq -o verify_schema.rust
mv verify_schema.rust verify_schema.rs
```

for `verify_schema.rs`.
