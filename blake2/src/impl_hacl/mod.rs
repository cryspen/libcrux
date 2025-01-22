extern crate alloc;

mod blake2b;
mod blake2s;
mod error;

pub use blake2b::{Blake2b, Blake2bBuilder};
pub use blake2s::{Blake2s, Blake2sBuilder};
pub use error::Error;

/// Type that holds the constants in case both key length and digest length are known at compile
/// time.
pub struct ConstsStaticKeyStaticOut<const KEY_LEN: usize, const OUT_LEN: usize>;

/// Type that holds the constant in case just the key length is known at compile time.
pub struct ConstsStaticKey<const KEY_LEN: usize>;

/// Type that holds the constant in case just the digest length is known at compile time.
pub struct ConstsStaticOut<const OUT_LEN: usize>;

/// Type that holds the constant in case neither the key length nor the digest length is known at
/// compile time.
pub struct ConstsDynamic;

#[cfg(test)]
mod test {
    use super::{Blake2bBuilder, Blake2sBuilder};

    #[test]
    fn test_blake2b() {
        let mut got_hash = [0; 32];

        // test unkeyed, with static key and digest len
        let expected_hash = b"\xe9\xed\x14\x1d\xf1\xce\xbf\xc8\x9e\x46\x6c\xe0\x89\xee\xdd\x4f\x12\x5a\xa7\x57\x15\x01\xa0\xaf\x87\x1f\xab\x60\x59\x71\x17\xb7";
        let mut hasher = Blake2bBuilder::new_unkeyed()
            .build_const_digest_len()
            .unwrap();
        hasher.update(b"this is a test").unwrap();
        hasher.finalize(&mut got_hash);

        assert_eq!(&got_hash, expected_hash);

        hasher.reset();
        hasher.update(b"this is a test").unwrap();
        hasher.finalize(&mut got_hash);

        assert_eq!(&got_hash, expected_hash);

        // test unkeyed, with static key len and dynamic digest len
        let mut hasher = Blake2bBuilder::new_unkeyed()
            .build_var_digest_len(32)
            .unwrap();
        hasher.update(b"this is a test").unwrap();
        hasher.finalize(&mut got_hash).unwrap();

        assert_eq!(&got_hash, expected_hash);

        hasher.reset();
        hasher.update(b"this is a test").unwrap();
        hasher.finalize(&mut got_hash).unwrap();

        assert_eq!(&got_hash, expected_hash);

        // test keyed, with static key and digest len
        let expected_hash = b"\x2a\xbb\x86\x16\xc6\x99\xe5\x1d\xa3\x65\xca\xb7\xad\xe0\x53\x92\xaf\xa2\xc3\xc6\x13\x08\x7f\x84\xb0\xd1\x6e\x5a\x4f\xab\xa7\xb8";
        let mut hasher = Blake2bBuilder::new_keyed_static(b"test")
            .unwrap()
            .build_const_digest_len()
            .unwrap();
        hasher.update(b"this is a test").unwrap();
        hasher.finalize(&mut got_hash);

        assert_eq!(&got_hash, expected_hash);

        hasher.reset_with_key(b"test");
        hasher.update(b"this is a test").unwrap();
        hasher.finalize(&mut got_hash);

        assert_eq!(&got_hash, expected_hash);

        // test keyed, with static key len and dynamic digest len
        let mut hasher = Blake2bBuilder::new_keyed_static(b"test")
            .unwrap()
            .build_var_digest_len(32)
            .unwrap();
        hasher.update(b"this is a test").unwrap();
        let len = hasher.finalize(&mut got_hash).unwrap();

        assert_eq!(len, 32);
        assert_eq!(&got_hash, expected_hash);

        hasher.reset_with_key(b"test");
        hasher.update(b"this is a test").unwrap();
        let len = hasher.finalize(&mut got_hash).unwrap();

        assert_eq!(&got_hash, expected_hash);
        assert_eq!(len, 32);

        // test keyed, with dynamic key len and static digest len
        let mut hasher = Blake2bBuilder::new_keyed_dynamic(b"test")
            .unwrap()
            .build_const_digest_len()
            .unwrap();
        hasher.update(b"this is a test").unwrap();
        hasher.finalize(&mut got_hash);

        assert_eq!(&got_hash, expected_hash);

        hasher.reset_with_key(b"test").unwrap();
        hasher.update(b"this is a test").unwrap();
        hasher.finalize(&mut got_hash);

        assert_eq!(&got_hash, expected_hash);

        // test keyed, with dynamic key digest len
        let mut hasher = Blake2bBuilder::new_keyed_dynamic(b"test")
            .unwrap()
            .build_var_digest_len(32)
            .unwrap();
        hasher.update(b"this is a test").unwrap();
        let len = hasher.finalize(&mut got_hash).unwrap();

        assert_eq!(len, 32);
        assert_eq!(&got_hash, expected_hash);

        hasher.reset_with_key(b"test").unwrap();
        hasher.update(b"this is a test").unwrap();
        let len = hasher.finalize(&mut got_hash).unwrap();

        assert_eq!(&got_hash, expected_hash);
        assert_eq!(len, 32);

        let mut got_hash = [0; 64];
        let mut hasher = Blake2bBuilder::new_unkeyed()
            .build_const_digest_len()
            .unwrap();
        hasher.update(b"this is a test").unwrap();
        hasher.finalize(&mut got_hash);
        let expected_hash = b"\x61\xa5\x48\xf2\xde\x1c\x31\x8b\xa9\x1d\x52\x07\x00\x78\x61\x01\x0f\x69\xa4\x3e\xc6\x63\xfe\x48\x7d\x84\x03\x28\x2c\x93\x4e\xa7\x25\xdc\x0b\xb1\x72\x25\x6a\xc9\x96\x25\xad\x64\xcc\xa6\xa2\xc4\xd6\x1c\x65\x0a\x35\xaf\xab\x47\x87\xdc\x67\x8e\x19\x07\x1e\xf9";

        assert_eq!(&got_hash, expected_hash);
    }

    #[test]
    fn test_blake2s() {
        let mut got_hash = [0; 32];

        // test unkeyed, with static key and digest len
        let expected_hash = b"\xf2\x01\x46\xc0\x54\xf9\xdd\x6b\x67\x64\xb6\xc0\x93\x57\xf7\xcd\x75\x51\xdf\xbc\xba\x54\x59\x72\xa4\xc8\x16\x6d\xf8\xaf\xde\x60";
        let mut hasher = Blake2sBuilder::new_unkeyed()
            .build_const_digest_len()
            .unwrap();
        hasher.update(b"this is a test").unwrap();
        hasher.finalize(&mut got_hash);

        assert_eq!(&got_hash, expected_hash);

        hasher.reset();
        hasher.update(b"this is a test").unwrap();
        hasher.finalize(&mut got_hash);

        assert_eq!(&got_hash, expected_hash);

        // test unkeyed, with static key len and dynamic digest len
        let expected_hash = b"\xf2\x01\x46\xc0\x54\xf9\xdd\x6b\x67\x64\xb6\xc0\x93\x57\xf7\xcd\x75\x51\xdf\xbc\xba\x54\x59\x72\xa4\xc8\x16\x6d\xf8\xaf\xde\x60";
        let mut hasher = Blake2sBuilder::new_unkeyed()
            .build_var_digest_len(32)
            .unwrap();
        hasher.update(b"this is a test").unwrap();
        hasher.finalize(&mut got_hash).unwrap();

        assert_eq!(&got_hash, expected_hash);

        hasher.reset();
        hasher.update(b"this is a test").unwrap();
        hasher.finalize(&mut got_hash).unwrap();

        assert_eq!(&got_hash, expected_hash);

        // test keyed, with static key and digest len
        let expected_hash = b"\x98\xfb\xfa\x89\xb3\xee\x07\x51\x9e\xe6\x2c\x18\xfe\x9d\x85\xdc\xf0\x83\x7b\x12\xae\x4d\xe7\x29\xf0\x7b\x55\xa9\x1a\x94\x80\xe8";
        let mut hasher = Blake2sBuilder::new_keyed_static(b"test")
            .unwrap()
            .build_const_digest_len()
            .unwrap();
        hasher.update(b"this is a test").unwrap();
        hasher.finalize(&mut got_hash);

        assert_eq!(&got_hash, expected_hash);

        hasher.reset_with_key(b"test");
        hasher.update(b"this is a test").unwrap();
        hasher.finalize(&mut got_hash);

        assert_eq!(&got_hash, expected_hash);

        // test keyed, with static key len and dynamic digest len
        let mut hasher = Blake2sBuilder::new_keyed_static(b"test")
            .unwrap()
            .build_var_digest_len(32)
            .unwrap();
        hasher.update(b"this is a test").unwrap();
        let len = hasher.finalize(&mut got_hash).unwrap();

        assert_eq!(len, 32);
        assert_eq!(&got_hash, expected_hash);

        hasher.reset_with_key(b"test");
        hasher.update(b"this is a test").unwrap();
        let len = hasher.finalize(&mut got_hash).unwrap();

        assert_eq!(&got_hash, expected_hash);
        assert_eq!(len, 32);

        // test keyed, with dynamic key len and static digest len
        let mut hasher = Blake2sBuilder::new_keyed_dynamic(b"test")
            .unwrap()
            .build_const_digest_len()
            .unwrap();
        hasher.update(b"this is a test").unwrap();
        hasher.finalize(&mut got_hash);

        assert_eq!(&got_hash, expected_hash);

        hasher.reset_with_key(b"test").unwrap();
        hasher.update(b"this is a test").unwrap();
        hasher.finalize(&mut got_hash);

        assert_eq!(&got_hash, expected_hash);

        // test keyed, with dynamic key digest len
        let mut hasher = Blake2sBuilder::new_keyed_dynamic(b"test")
            .unwrap()
            .build_var_digest_len(32)
            .unwrap();
        hasher.update(b"this is a test").unwrap();
        let len = hasher.finalize(&mut got_hash).unwrap();

        assert_eq!(len, 32);
        assert_eq!(&got_hash, expected_hash);

        hasher.reset_with_key(b"test").unwrap();
        hasher.update(b"this is a test").unwrap();
        let len = hasher.finalize(&mut got_hash).unwrap();

        assert_eq!(&got_hash, expected_hash);
        assert_eq!(len, 32);
    }
}
