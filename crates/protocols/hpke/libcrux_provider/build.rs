fn main() {
    // The `draft-connolly-cfrg-hpke-mlkem` feature is deprecated in favour of
    // `draft-ietf-hpke-pq`. Warn at build time when it is enabled.
    if std::env::var_os("CARGO_FEATURE_DRAFT_CONNOLLY_CFRG_HPKE_MLKEM").is_some() {
        println!(
            "cargo:warning=the `draft-connolly-cfrg-hpke-mlkem` feature is deprecated; \
             use `draft-ietf-hpke-pq` instead"
        );
    }
}
