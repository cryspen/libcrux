// Test vectors defined once for reuse across all implementations
mod test_vectors {
    pub const EMPTY: &[u8] = b"";
    pub const HELLO: &[u8] = b"Hello, World!";
    pub const FOX: &[u8] = b"The quick brown fox jumps over the lazy dog";

    pub mod sha3_224 {
        pub const HELLO: &str = "853048fb8b11462b6100385633c0cc8dcdc6e2b8e376c28102bc84f2";
        pub const FOX: &str = "d15dadceaa4d5d7bb3b48f446421d542e08ad8887305e28d58335795";
        pub const EMPTY: &str = "6b4e03423667dbb73b6e15454f0eb1abd4597f9a1b078e3f5b5a6bc7";
    }

    pub mod sha3_256 {
        pub const HELLO: &str = "1af17a664e3fa8e419b8ba05c2a173169df76162a5a286e0c405b460d478f7ef";
        pub const FOX: &str = "69070dda01975c8c120c3aada1b282394e7f032fa9cf32f4cb2259a0897dfc04";
        pub const EMPTY: &str = "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a";
    }

    pub mod sha3_384 {
        pub const HELLO: &str =
            "aa9ad8a49f31d2ddcabbb7010a1566417cff803fef50eba239558826f872e468c5\
                  743e7f026b0a8e5b2d7a1cc465cdbe";
        pub const FOX: &str =
            "7063465e08a93bce31cd89d2e3ca8f602498696e253592ed26f07bf7e703cf328581\
                  e1471a7ba7ab119b1a9ebdf8be41";
        pub const EMPTY: &str =
            "0c63a75b845e4f7d01107d852e4c2485c51a50aaaa94fc61995e71bbee983a2ac3\
                  713831264adb47fb6bd1e058d5f004";
    }

    pub mod sha3_512 {
        pub const HELLO: &str =
            "38e05c33d7b067127f217d8c856e554fcff09c9320b8a5979ce2ff5d95dd27ba35\
                  d1fba50c562dfd1d6cc48bc9c5baa4390894418cc942d968f97bcb659419ed";
        pub const FOX: &str =
            "01dedd5de4ef14642445ba5f5b97c15e47b9ad931326e4b0727cd94cefc44fff23f0\
                  7bf543139939b49128caf436dc1bdee54fcb24023a08d9403f9b4bf0d450";
        pub const EMPTY: &str =
            "a69f73cca23a9ac5c8b567dc185a756e97c982164fe25859e0d1dcc1475c80a615\
                  b2123af1f5f94c11e3e9402c3ac558f500199d95b6d3e301758586281dcd26";
    }

    pub mod shake128 {
        pub const HELLO_FIVE_BLOCKS: &str =
            "2bf5e6dee6079fad604f573194ba8426bd4d30eb13e8ba2edae70e529b570cbdd\
                  588f2c5dd4e465dfbafaa7c5634249c8929dc04165a9edb26be19ce03619\
                  6d178454d03b738b0d6b40013954208e40214908a8d388f9a9d997e2e381\
                  f571dec1dfa816df96e3cb635e99a8d7d072fac7b7664d45a7a43b258cbe\
                  290a4c735977a9a8e9c363564f2e13c80f1e3611907a09756a7ba87e07f5\
                  4856489d2edae1634afed8503ab6561d79b0fbb64f75a9822335c2fc7017\
                  8114b4460c979a22c78c4890c611b0cf5091f2ac4aff35d190832a36bc61\
                  9f0e66fcb7c32044293207c15a686bd1f5f2a314147a583454826fd43874\
                  7784cf715e13008adf597dcd3cd87f633dc8a80bbd6a18bdd02551697d8c\
                  66009961645875c8ad37c2fbc81c7727cbb99dcd8fba52e91a6a8580c284\
                  6430a629a150492a3a2d93bf93c8b704e0a05fa891bdf8aee78f646cd06e\
                  357acf909982e864375059076fe2079ddcc4227a479ff6cb72eec7a4fca4\
                  edf94c014c9f725d9704afbb265e611f705c696e6e02cf166007c0cd7d93\
                  50901033d4f26fa74b13f9a40515756753c56412c1662c3e1d118df42f41\
                  780ba028b6a650a3cef7a7fe07f0f2f18f33a08fe21b55d0a6effc6dd3dc\
                  753e1c2686ca428863731ce17cfd06ae7396cfbc5cbe05745fd89e822469\
                  b459e1266d7c0b96ac63d61de57710afef99ab06329c5809a9f47f914e1a\
                  ff52f0883a6be14ed361af6cdb6e5146eac04fb704ade9154f94d88807c9\
                  8d4aea95f6f25e6e71cded62cfcc7cd2fd0c7a29b3e9c284282fa4744004\
                  b98902ce6ae90e2d310a1c71227ca7602a4a8f7d44eda895ef2c85280e4c\
                  1d35f351761ca598ec19fdee75feb5a44368600f735e6b17d8d6000570b4\
                  b35940b18334835d06d2537f398c0d04fd354fa100840f865ba2b30818c5\
                  f56ed7af478cd0be37b3e3486257bf2c092f9477c16b1918d15c33c7bce0\
                  63440699b0a3407570f9076abf19f33aaee83d5fa2abdc81e9380df2b2d6\
                  5511dfce21bd969dc69a99aa5bdc1cbf0c7410f9f5da0f6403243562accb\
                  c99fc734804563770d518c27aa3f9e2714d8e945b4df71d5c4d6b6d91e2f\
                  981ff84e260e2011618bbd3d59ec07948eee3de448b8916d19fda8152f55\
                  78108506cdb5b8103956dc80c789085c0af06483a9892e4b1ff0d97";
        pub const FOX_53: &str =
            "f4202e3c5852f9182a0430fd8144f0a74b95e7417ecae17db0f8cfeed0e3e66eb\
                  5585ec6f86021cacf272c798bcf97d368b886b18f";
    }

    pub mod shake256 {
        pub const HELLO_FIVE_BLOCKS: &str =
            "b3be97bfd978833a65588ceae8a34cf59e95585af62063e6b89d0789f372424e8\
                  b0d1be4f21b40ce5a83a438473271e0661854f02d431db74e6904d6c347d\
                  757a33b44f18e740bd119782f48b0ac4ee1fa2dee4c5018ee2f186d0ff94\
                  d1cece111e29a6bbd0972cb8574b5afddd55f00e50bd402c998043ba3f45\
                  53558391be010abb209af935224b8c331d0d29c008185f2c900abad89885\
                  1c4f3d941a13f03e3c315c4fb058fca2bb4e2bc53fec7866eb7e7636f276\
                  dc5a167cad77b286c9a94946fe054927c48db7f30424787f56153cc67ca4\
                  9609928d24c16563d3a0aaad1ca1495003374868ec422a72bedd2f387abc\
                  350b46a9a6580a3ceb56b602b7edab836d58d8bb6b1a6975aaad42554132\
                  71ec544ddea12dbb65003da4273650d6e3b51373e4e86fced975dad607ad\
                  d1184702952d4bf8459d05197293d35b59688a9f13806887f9845211eb2d\
                  0b9cc1e089eba8c16f9967d80ec181a754ea6511a897c736ba4c09871d99\
                  3a41cf7efb08f0479935eaa811865002353f39594d432417d0e70d371509\
                  bb0b76003e9712354427ab1e4f69ebd5e32b585166b3e843b062efa32bc7\
                  1bbdc0989b87137752452a8a908ccea6ee1980e9213c6a380cdb947be228\
                  5416b088ee4646793286d44b25df89575df2ef08a4c78237e7e25ec8b3a3\
                  af7a63c0aa0fd46582874ab9417fb4e720298a4d6de8faa6f71a4ef4e6a1\
                  4a5dcce0f002465987e661e9ed0d39fa79d018572ac40613630bf68868de\
                  5cbe1e33eb014cdeeb125f8842fd1b0bd3c4970f2ddb9a3db5cdd0ca7e37\
                  785d2029bbe2e6a8a225265fbbdd12e9712a538f5a346eeab6f9cc296580\
                  e6d7c274d07084e758d01006b22bd45778ecb86bb495d413aef4dc28aa84\
                  8f46cbe4e189fb0d3de54bf2c146d280b163e9358200547ee71207f11a4e\
                  25e643a4552d6971cf4efb277a7d1d10095";

        pub const FOX_71: &str =
            "2f671343d9b2e1604dc9dcf0753e5fe15c7c64a0d283cbbf722d411a0e36f6ca1\
                  d01d1369a23539cd80f7c054b6e5daf9c962cad5b8ed5bd11998b40d5734442bed798f6e5c915";
    }
}

// Portable implementation tests
mod portable {
    use super::test_vectors;
    use libcrux_sha3::portable::{incremental, sha224, sha256, sha384, sha512, shake128, shake256};

    #[test]
    fn sha3_224() {
        let mut digest = [0u8; 28];

        sha224(&mut digest, test_vectors::EMPTY);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_224::EMPTY);

        sha224(&mut digest, test_vectors::HELLO);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_224::HELLO);

        sha224(&mut digest, test_vectors::FOX);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_224::FOX);
    }

    #[test]
    fn sha3_256() {
        let mut digest = [0u8; 32];

        sha256(&mut digest, test_vectors::EMPTY);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_256::EMPTY);

        sha256(&mut digest, test_vectors::HELLO);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_256::HELLO);

        sha256(&mut digest, test_vectors::FOX);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_256::FOX);
    }

    #[test]
    fn sha3_384() {
        let mut digest = [0u8; 48];

        sha384(&mut digest, test_vectors::EMPTY);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_384::EMPTY);

        sha384(&mut digest, test_vectors::HELLO);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_384::HELLO);

        sha384(&mut digest, test_vectors::FOX);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_384::FOX);
    }

    #[test]
    fn sha3_512() {
        let mut digest = [0u8; 64];

        sha512(&mut digest, test_vectors::EMPTY);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_512::EMPTY);

        sha512(&mut digest, test_vectors::HELLO);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_512::HELLO);

        sha512(&mut digest, test_vectors::FOX);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_512::FOX);
    }

    #[test]
    fn sha3_shake128() {
        let mut digest = [0u8; 42];

        shake128(&mut digest, test_vectors::HELLO);
        assert_eq!(
            hex::encode(&digest),
            &test_vectors::shake128::HELLO_FIVE_BLOCKS[..84]
        );

        let mut digest = [0u8; 53];

        shake128(&mut digest, test_vectors::FOX);
        assert_eq!(hex::encode(&digest), test_vectors::shake128::FOX_53);
    }

    #[test]
    fn sha3_shake256() {
        let mut digest = [0u8; 42];

        shake256(&mut digest, test_vectors::HELLO);
        assert_eq!(
            hex::encode(&digest),
            &test_vectors::shake256::HELLO_FIVE_BLOCKS[..84]
        );

        let mut digest = [0u8; 71];

        shake256(&mut digest, test_vectors::FOX);
        assert_eq!(hex::encode(&digest), test_vectors::shake256::FOX_71);
    }

    #[test]
    fn sha3_shake128_incremental() {
        // Test squeezing 1 block (168 bytes)
        let mut state = incremental::shake128_init();
        incremental::shake128_absorb_final(&mut state, test_vectors::HELLO);

        let mut digest = [0u8; 168];
        incremental::shake128_squeeze_first_block(&mut state, &mut digest);
        assert_eq!(
            hex::encode(&digest),
            &test_vectors::shake128::HELLO_FIVE_BLOCKS[..336]
        );

        // Test squeezing next block (168 bytes)
        incremental::shake128_squeeze_next_block(&mut state, &mut digest);
        assert_eq!(
            hex::encode(&digest),
            &test_vectors::shake128::HELLO_FIVE_BLOCKS[336..672]
        );

        // ---

        // Test squeezing 3 blocks (504 bytes)
        state = incremental::shake128_init();
        incremental::shake128_absorb_final(&mut state, test_vectors::HELLO);

        let mut digest = [0u8; 504];
        incremental::shake128_squeeze_first_three_blocks(&mut state, &mut digest);
        assert_eq!(
            hex::encode(&digest),
            &test_vectors::shake128::HELLO_FIVE_BLOCKS[..1008]
        );

        // ---

        // Test squeezing 5 blocks (840 bytes)
        state = incremental::shake128_init();
        incremental::shake128_absorb_final(&mut state, test_vectors::HELLO);

        let mut digest = [0u8; 840];
        incremental::shake128_squeeze_first_five_blocks(&mut state, &mut digest);
        assert_eq!(
            hex::encode(&digest),
            test_vectors::shake128::HELLO_FIVE_BLOCKS
        );
    }

    #[test]
    fn sha3_shake256_incremental() {
        // Test squeezing 1 block (136 bytes for SHAKE256, not 168)
        let mut state = incremental::shake256_init();
        incremental::shake256_absorb_final(&mut state, test_vectors::HELLO);

        let mut digest = [0u8; 136];
        incremental::shake256_squeeze_first_block(&mut state, &mut digest);
        assert_eq!(
            hex::encode(&digest),
            &test_vectors::shake256::HELLO_FIVE_BLOCKS[..272]
        );

        // Test squeezing next block (136 bytes)
        incremental::shake256_squeeze_next_block(&mut state, &mut digest);
        assert_eq!(
            hex::encode(&digest),
            &test_vectors::shake256::HELLO_FIVE_BLOCKS[272..544]
        );

        // Test squeezing 3 blocks (408 bytes = 3 * 136)
        state = incremental::shake256_init();
        incremental::shake256_absorb_final(&mut state, test_vectors::HELLO);

        let mut digest = [0u8; 408];
        incremental::shake256_squeeze_first_three_blocks(&mut state, &mut digest);
        assert_eq!(
            hex::encode(&digest),
            &test_vectors::shake256::HELLO_FIVE_BLOCKS[..816]
        );

        // Test squeezing 5 blocks (680 bytes = 5 * 136)
        state = incremental::shake256_init();
        incremental::shake256_absorb_final(&mut state, test_vectors::HELLO);

        let mut digest = [0u8; 680];
        incremental::shake256_squeeze_first_five_blocks(&mut state, &mut digest);
        assert_eq!(
            hex::encode(&digest),
            &test_vectors::shake256::HELLO_FIVE_BLOCKS[..1360]
        );
    }
}

// ARM specific tests
#[cfg(feature = "simd128")]
mod neon {
    use super::test_vectors;
    use libcrux_sha3::neon::{incremental, sha224, sha256, sha384, sha512, shake128, shake256};

    #[test]
    fn sha3_224() {
        let mut digest = [0u8; 28];

        sha224(&mut digest, test_vectors::EMPTY);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_224::EMPTY);

        sha224(&mut digest, test_vectors::HELLO);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_224::HELLO);

        sha224(&mut digest, test_vectors::FOX);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_224::FOX);
    }

    #[test]
    fn sha3_256() {
        let mut digest = [0u8; 32];

        sha256(&mut digest, test_vectors::EMPTY);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_256::EMPTY);

        sha256(&mut digest, test_vectors::HELLO);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_256::HELLO);

        sha256(&mut digest, test_vectors::FOX);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_256::FOX);
    }

    #[test]
    fn sha3_384() {
        let mut digest = [0u8; 48];

        sha384(&mut digest, test_vectors::EMPTY);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_384::EMPTY);

        sha384(&mut digest, test_vectors::HELLO);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_384::HELLO);

        sha384(&mut digest, test_vectors::FOX);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_384::FOX);
    }

    #[test]
    fn sha3_512() {
        let mut digest = [0u8; 64];

        sha512(&mut digest, test_vectors::EMPTY);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_512::EMPTY);

        sha512(&mut digest, test_vectors::HELLO);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_512::HELLO);

        sha512(&mut digest, test_vectors::FOX);
        assert_eq!(hex::encode(&digest), test_vectors::sha3_512::FOX);
    }

    #[test]
    fn sha3_shake128() {
        let mut digest = [0u8; 42];

        shake128(&mut digest, test_vectors::HELLO);
        assert_eq!(
            hex::encode(&digest),
            &test_vectors::shake128::HELLO_FIVE_BLOCKS[..84]
        );

        let mut digest = [0u8; 53];

        shake128(&mut digest, test_vectors::FOX);
        assert_eq!(hex::encode(&digest), test_vectors::shake128::FOX_53);
    }

    #[test]
    fn sha3_shake256() {
        let mut digest = [0u8; 42];

        shake256(&mut digest, test_vectors::HELLO);
        assert_eq!(
            hex::encode(&digest),
            &test_vectors::shake256::HELLO_FIVE_BLOCKS[..84]
        );

        let mut digest = [0u8; 71];

        shake256(&mut digest, test_vectors::FOX);
        assert_eq!(hex::encode(&digest), test_vectors::shake256::FOX_71);
    }

    #[test]
    fn sha3_shake128_incremental() {
        // Test squeezing 1 block (168 bytes)
        let mut state = incremental::shake128_init();
        incremental::shake128_absorb_final(&mut state, test_vectors::HELLO);

        let mut digest = [0u8; 168];
        incremental::shake128_squeeze_first_block(&mut state, &mut digest);
        assert_eq!(
            hex::encode(&digest),
            &test_vectors::shake128::HELLO_FIVE_BLOCKS[..336]
        );

        // Test squeezing next block (168 bytes)
        incremental::shake128_squeeze_next_block(&mut state, &mut digest);
        assert_eq!(
            hex::encode(&digest),
            &test_vectors::shake128::HELLO_FIVE_BLOCKS[336..672]
        );

        // ---

        // Test squeezing 3 blocks (504 bytes)
        state = incremental::shake128_init();
        incremental::shake128_absorb_final(&mut state, test_vectors::HELLO);

        let mut digest = [0u8; 504];
        incremental::shake128_squeeze_first_three_blocks(&mut state, &mut digest);
        assert_eq!(
            hex::encode(&digest),
            &test_vectors::shake128::HELLO_FIVE_BLOCKS[..1008]
        );

        // ---

        // Test squeezing 5 blocks (840 bytes)
        state = incremental::shake128_init();
        incremental::shake128_absorb_final(&mut state, test_vectors::HELLO);

        let mut digest = [0u8; 840];
        incremental::shake128_squeeze_first_five_blocks(&mut state, &mut digest);
        assert_eq!(
            hex::encode(&digest),
            test_vectors::shake128::HELLO_FIVE_BLOCKS
        );
    }

    #[test]
    fn sha3_shake256_incremental() {
        // Test squeezing 1 block (136 bytes for SHAKE256, not 168)
        let mut state = incremental::shake256_init();
        incremental::shake256_absorb_final(&mut state, test_vectors::HELLO);

        let mut digest = [0u8; 136];
        incremental::shake256_squeeze_first_block(&mut state, &mut digest);
        assert_eq!(
            hex::encode(&digest),
            &test_vectors::shake256::HELLO_FIVE_BLOCKS[..272]
        );

        // Test squeezing next block (136 bytes)
        incremental::shake256_squeeze_next_block(&mut state, &mut digest);
        assert_eq!(
            hex::encode(&digest),
            &test_vectors::shake256::HELLO_FIVE_BLOCKS[272..544]
        );

        // Test squeezing 3 blocks (408 bytes = 3 * 136)
        state = incremental::shake256_init();
        incremental::shake256_absorb_final(&mut state, test_vectors::HELLO);

        let mut digest = [0u8; 408];
        incremental::shake256_squeeze_first_three_blocks(&mut state, &mut digest);
        assert_eq!(
            hex::encode(&digest),
            &test_vectors::shake256::HELLO_FIVE_BLOCKS[..816]
        );

        // Test squeezing 5 blocks (680 bytes = 5 * 136)
        state = incremental::shake256_init();
        incremental::shake256_absorb_final(&mut state, test_vectors::HELLO);

        let mut digest = [0u8; 680];
        incremental::shake256_squeeze_first_five_blocks(&mut state, &mut digest);
        assert_eq!(
            hex::encode(&digest),
            &test_vectors::shake256::HELLO_FIVE_BLOCKS[..1360]
        );
    }
}

#[test]
fn sha3_kat_oneshot() {
    let d256 = libcrux_sha3::sha256(b"Hello, World!");
    let expected256 = "1af17a664e3fa8e419b8ba05c2a173169df76162a5a286e0c405b460d478f7ef";
    assert_eq!(hex::encode(&d256), expected256);

    let dshake = libcrux_sha3::shake128::<42>(b"Hello, World!");
    let expectedshake =
        "2bf5e6dee6079fad604f573194ba8426bd4d30eb13e8ba2edae70e529b570cbdd588f2c5dd4e465dfbaf";
    assert_eq!(hex::encode(&dshake), expectedshake);
}

#[test]
fn sha3_simd_kat_oneshot() {
    let d256 = libcrux_sha3::sha256(b"Hello, World!");
    let expected256 = "1af17a664e3fa8e419b8ba05c2a173169df76162a5a286e0c405b460d478f7ef";
    assert_eq!(hex::encode(&d256), expected256);

    let dshake = libcrux_sha3::shake128::<42>(b"Hello, World!");
    let expectedshake =
        "2bf5e6dee6079fad604f573194ba8426bd4d30eb13e8ba2edae70e529b570cbdd588f2c5dd4e465dfbaf";
    assert_eq!(hex::encode(&dshake), expectedshake);
}
