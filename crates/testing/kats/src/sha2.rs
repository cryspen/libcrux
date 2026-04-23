pub use cavp::{Sha3 as Hash, TestVector};

macro_rules! load_fn {
    ($name:ident, $file:literal) => {
        pub fn $name() -> TestVector<Hash> {
            cavp::read_string(include_str!($file)).expect("failed to parse CAVP test vector")
        }
    };
}

load_fn!(sha224_short, "tv/SHA224ShortMsg.rsp");
load_fn!(sha224_long, "tv/SHA224LongMsg.rsp");
load_fn!(sha256_short, "tv/SHA256ShortMsg.rsp");
load_fn!(sha256_long, "tv/SHA256LongMsg.rsp");
load_fn!(sha384_short, "tv/SHA384ShortMsg.rsp");
load_fn!(sha384_long, "tv/SHA384LongMsg.rsp");
load_fn!(sha512_short, "tv/SHA512ShortMsg.rsp");
load_fn!(sha512_long, "tv/SHA512LongMsg.rsp");
