use libcrux_sha3::{digest_size, portable::incremental};

#[test]
fn sha224() {
    let digest = libcrux_sha3::sha224(b"Hello, World!");
    let expected = "853048fb8b11462b6100385633c0cc8dcdc6e2b8e376c28102bc84f2";
    assert_eq!(hex::encode(&digest), expected);

    let digest = libcrux_sha3::sha224(b"38e05c33d7b067127f217d8c856e554fcff09c9320b8a5979ce2ff5d95dd27ba35d1fba50c562dfd1d6cc48bc9c5baa4390894418cc942d968f97bcb659419ed");
    let expected = "7a6d978891d9d5aadd6e5f129fed74cefe530ee2905c1cef1fc07af0";
    assert_eq!(hex::encode(&digest), expected);

    #[cfg(feature = "simd128")]
    {
        let mut digest = [0u8; digest_size(libcrux_sha3::Algorithm::Sha224)];
        libcrux_sha3::neon::sha224(&mut digest, b"Hello, World!");
        let expected = "853048fb8b11462b6100385633c0cc8dcdc6e2b8e376c28102bc84f2";
        assert_eq!(hex::encode(&digest), expected);
    }
}

#[test]
fn sha256() {
    let digest = libcrux_sha3::sha256(b"Hello, World!");
    let expected = "1af17a664e3fa8e419b8ba05c2a173169df76162a5a286e0c405b460d478f7ef";
    assert_eq!(hex::encode(&digest), expected);

    #[cfg(feature = "simd128")]
    {
        let mut digest = [0u8; digest_size(libcrux_sha3::Algorithm::Sha256)];
        libcrux_sha3::neon::sha256(&mut digest, b"Hello, World!");
        let expected = "1af17a664e3fa8e419b8ba05c2a173169df76162a5a286e0c405b460d478f7ef";
        assert_eq!(hex::encode(&digest), expected);
    }
}

#[test]
fn sha384() {
    let digest = libcrux_sha3::sha384(b"Hello, World!");
    let expected = "aa9ad8a49f31d2ddcabbb7010a1566417cff803fef50eba239558826f872e468c5743e7f026b0a8e5b2d7a1cc465cdbe";
    assert_eq!(hex::encode(&digest), expected);

    #[cfg(feature = "simd128")]
    {
        let mut digest = [0u8; digest_size(libcrux_sha3::Algorithm::Sha384)];
        libcrux_sha3::neon::sha384(&mut digest, b"Hello, World!");
        let expected = "aa9ad8a49f31d2ddcabbb7010a1566417cff803fef50eba239558826f872e468c5743e7f026b0a8e5b2d7a1cc465cdbe";
        assert_eq!(hex::encode(&digest), expected);
    }
}

#[test]
fn sha512() {
    let digest = libcrux_sha3::sha512(b"Hello, World!");
    let expected = "38e05c33d7b067127f217d8c856e554fcff09c9320b8a5979ce2ff5d95dd27ba35d1fba50c562dfd1d6cc48bc9c5baa4390894418cc942d968f97bcb659419ed";
    assert_eq!(hex::encode(&digest), expected);

    let digest = libcrux_sha3::sha512(b"38e05c33d7b067127f217d8c856e554fcff09c9320b8a5979ce2ff5d95dd27ba35d1fba50c562dfd1d6cc48bc9c5baa4390894418cc942d968f97bcb659419ed");
    let expected = "24cd4c386a4d4233958643da9a2d6a88bda8604dd56375579dac6fad280e4beae18c9350cd73bd7c1af8a290e4a7a7a7f8cafe2e880aae02710df4d9e92b0726";
    assert_eq!(hex::encode(&digest), expected);

    #[cfg(feature = "simd128")]
    {
        let mut digest = [0u8; digest_size(libcrux_sha3::Algorithm::Sha512)];
        libcrux_sha3::neon::sha512(&mut digest, b"Hello, World!");
        let expected = "38e05c33d7b067127f217d8c856e554fcff09c9320b8a5979ce2ff5d95dd27ba35d1fba50c562dfd1d6cc48bc9c5baa4390894418cc942d968f97bcb659419ed";
        assert_eq!(hex::encode(&digest), expected);
    }
}

#[test]
fn shake128() {
    let digest = libcrux_sha3::shake128::<42>(b"Hello, World!");
    let expected =
        "2bf5e6dee6079fad604f573194ba8426bd4d30eb13e8ba2edae70e529b570cbdd588f2c5dd4e465dfbaf";
    assert_eq!(hex::encode(&digest), expected);

    let digest = libcrux_sha3::shake128::<377>(b"Hello, World!");
    let expected =
        "2bf5e6dee6079fad604f573194ba8426bd4d30eb13e8ba2edae70e529b570cbdd588f2c5dd4e465dfbafaa7c5634249c8929dc04165a9edb26be19ce036196d178454d03b738b0d6b40013954208e40214908a8d388f9a9d997e2e381f571dec1dfa816df96e3cb635e99a8d7d072fac7b7664d45a7a43b258cbe290a4c735977a9a8e9c363564f2e13c80f1e3611907a09756a7ba87e07f54856489d2edae1634afed8503ab6561d79b0fbb64f75a9822335c2fc70178114b4460c979a22c78c4890c611b0cf5091f2ac4aff35d190832a36bc619f0e66fcb7c32044293207c15a686bd1f5f2a314147a583454826fd438747784cf715e13008adf597dcd3cd87f633dc8a80bbd6a18bdd02551697d8c66009961645875c8ad37c2fbc81c7727cbb99dcd8fba52e91a6a8580c2846430a629a150492a3a2d93bf93c8b704e0a05fa891bdf8aee78f646cd06e357acf909982e864375059076fe2079ddcc4227a479ff6cb72eec7a4fca4edf94c014c9f725d9704afbb265e6";
    assert_eq!(hex::encode(&digest), expected);

    let mut shake = incremental::shake128_init();
    incremental::shake128_absorb_final(&mut shake, b"Hello, World!");
    let mut shaken = [0u8; 504]; // 3 blocks
    incremental::shake128_squeeze_first_three_blocks(&mut shake, &mut shaken);
    let expected = "2bf5e6dee6079fad604f573194ba8426bd4d30eb13e8ba2edae70e529b570cbdd588f2c5dd4e465dfbafaa7c5634249c8929dc04165a9edb26be19ce036196d178454d03b738b0d6b40013954208e40214908a8d388f9a9d997e2e381f571dec1dfa816df96e3cb635e99a8d7d072fac7b7664d45a7a43b258cbe290a4c735977a9a8e9c363564f2e13c80f1e3611907a09756a7ba87e07f54856489d2edae1634afed8503ab6561d79b0fbb64f75a9822335c2fc70178114b4460c979a22c78c4890c611b0cf5091f2ac4aff35d190832a36bc619f0e66fcb7c32044293207c15a686bd1f5f2a314147a583454826fd438747784cf715e13008adf597dcd3cd87f633dc8a80bbd6a18bdd02551697d8c66009961645875c8ad37c2fbc81c7727cbb99dcd8fba52e91a6a8580c2846430a629a150492a3a2d93bf93c8b704e0a05fa891bdf8aee78f646cd06e357acf909982e864375059076fe2079ddcc4227a479ff6cb72eec7a4fca4edf94c014c9f725d9704afbb265e611f705c696e6e02cf166007c0cd7d9350901033d4f26fa74b13f9a40515756753c56412c1662c3e1d118df42f41780ba028b6a650a3cef7a7fe07f0f2f18f33a08fe21b55d0a6effc6dd3dc753e1c2686ca428863731ce17cfd06ae7396cfbc5cbe05745fd89e822469b459e1266d7c0b96ac63d61de57710afef99ab06329";
    assert_eq!(hex::encode(&shaken), expected);

    #[cfg(feature = "simd128")]
    {
        use libcrux_sha3::neon::x2::incremental;

        let mut shake = incremental::init();
        incremental::shake128_absorb_final(&mut shake, b"Hello, World!", b"Hello, World!");

        let mut shaken0 = [0u8; 504]; // 3 blocks
        let mut shaken1 = [0u8; 504]; // 3 blocks
        incremental::shake128_squeeze_first_three_blocks(&mut shake, &mut shaken0, &mut shaken1);

        let expected = "2bf5e6dee6079fad604f573194ba8426bd4d30eb13e8ba2edae70e529b570cbdd588f2c5dd4e465dfbafaa7c5634249c8929dc04165a9edb26be19ce036196d178454d03b738b0d6b40013954208e40214908a8d388f9a9d997e2e381f571dec1dfa816df96e3cb635e99a8d7d072fac7b7664d45a7a43b258cbe290a4c735977a9a8e9c363564f2e13c80f1e3611907a09756a7ba87e07f54856489d2edae1634afed8503ab6561d79b0fbb64f75a9822335c2fc70178114b4460c979a22c78c4890c611b0cf5091f2ac4aff35d190832a36bc619f0e66fcb7c32044293207c15a686bd1f5f2a314147a583454826fd438747784cf715e13008adf597dcd3cd87f633dc8a80bbd6a18bdd02551697d8c66009961645875c8ad37c2fbc81c7727cbb99dcd8fba52e91a6a8580c2846430a629a150492a3a2d93bf93c8b704e0a05fa891bdf8aee78f646cd06e357acf909982e864375059076fe2079ddcc4227a479ff6cb72eec7a4fca4edf94c014c9f725d9704afbb265e611f705c696e6e02cf166007c0cd7d9350901033d4f26fa74b13f9a40515756753c56412c1662c3e1d118df42f41780ba028b6a650a3cef7a7fe07f0f2f18f33a08fe21b55d0a6effc6dd3dc753e1c2686ca428863731ce17cfd06ae7396cfbc5cbe05745fd89e822469b459e1266d7c0b96ac63d61de57710afef99ab06329";
        assert_eq!(hex::encode(&shaken0), expected);
        assert_eq!(shaken0, shaken1);

        let mut shake = incremental::init();
        incremental::shake128_absorb_final(&mut shake, b"Hello, World!", b"Hello, World!");

        let mut shaken0 = [0u8; 840]; // 5 blocks
        let mut shaken1 = [0u8; 840]; // 5 blocks
        incremental::shake128_squeeze_first_five_blocks(&mut shake, &mut shaken0, &mut shaken1);

        let expected = "2bf5e6dee6079fad604f573194ba8426bd4d30eb13e8ba2edae70e529b570cbdd588f2c5dd4e465dfbafaa7c5634249c8929dc04165a9edb26be19ce036196d178454d03b738b0d6b40013954208e40214908a8d388f9a9d997e2e381f571dec1dfa816df96e3cb635e99a8d7d072fac7b7664d45a7a43b258cbe290a4c735977a9a8e9c363564f2e13c80f1e3611907a09756a7ba87e07f54856489d2edae1634afed8503ab6561d79b0fbb64f75a9822335c2fc70178114b4460c979a22c78c4890c611b0cf5091f2ac4aff35d190832a36bc619f0e66fcb7c32044293207c15a686bd1f5f2a314147a583454826fd438747784cf715e13008adf597dcd3cd87f633dc8a80bbd6a18bdd02551697d8c66009961645875c8ad37c2fbc81c7727cbb99dcd8fba52e91a6a8580c2846430a629a150492a3a2d93bf93c8b704e0a05fa891bdf8aee78f646cd06e357acf909982e864375059076fe2079ddcc4227a479ff6cb72eec7a4fca4edf94c014c9f725d9704afbb265e611f705c696e6e02cf166007c0cd7d9350901033d4f26fa74b13f9a40515756753c56412c1662c3e1d118df42f41780ba028b6a650a3cef7a7fe07f0f2f18f33a08fe21b55d0a6effc6dd3dc753e1c2686ca428863731ce17cfd06ae7396cfbc5cbe05745fd89e822469b459e1266d7c0b96ac63d61de57710afef99ab06329c5809a9f47f914e1aff52f0883a6be14ed361af6cdb6e5146eac04fb704ade9154f94d88807c98d4aea95f6f25e6e71cded62cfcc7cd2fd0c7a29b3e9c284282fa4744004b98902ce6ae90e2d310a1c71227ca7602a4a8f7d44eda895ef2c85280e4c1d35f351761ca598ec19fdee75feb5a44368600f735e6b17d8d6000570b4b35940b18334835d06d2537f398c0d04fd354fa100840f865ba2b30818c5f56ed7af478cd0be37b3e3486257bf2c092f9477c16b1918d15c33c7bce063440699b0a3407570f9076abf19f33aaee83d5fa2abdc81e9380df2b2d65511dfce21bd969dc69a99aa5bdc1cbf0c7410f9f5da0f6403243562accbc99fc734804563770d518c27aa3f9e2714d8e945b4df71d5c4d6b6d91e2f981ff84e260e2011618bbd3d59ec07948eee3de448b8916d19fda8152f5578108506cdb5b8103956dc80c789085c0af06483a9892e4b1ff0d97";
        assert_eq!(hex::encode(&shaken0), expected);
        assert_eq!(shaken0, shaken1);
    }
}

#[test]
fn shake256() {
    let digest = libcrux_sha3::shake256::<42>(b"Hello, World!");
    let expected =
        "b3be97bfd978833a65588ceae8a34cf59e95585af62063e6b89d0789f372424e8b0d1be4f21b40ce5a83";
    assert_eq!(hex::encode(&digest), expected);

    let digest = libcrux_sha3::shake256::<377>(b"Hello, World!");
    let expected =
        "b3be97bfd978833a65588ceae8a34cf59e95585af62063e6b89d0789f372424e8b0d1be4f21b40ce5a83a438473271e0661854f02d431db74e6904d6c347d757a33b44f18e740bd119782f48b0ac4ee1fa2dee4c5018ee2f186d0ff94d1cece111e29a6bbd0972cb8574b5afddd55f00e50bd402c998043ba3f4553558391be010abb209af935224b8c331d0d29c008185f2c900abad898851c4f3d941a13f03e3c315c4fb058fca2bb4e2bc53fec7866eb7e7636f276dc5a167cad77b286c9a94946fe054927c48db7f30424787f56153cc67ca49609928d24c16563d3a0aaad1ca1495003374868ec422a72bedd2f387abc350b46a9a6580a3ceb56b602b7edab836d58d8bb6b1a6975aaad4255413271ec544ddea12dbb65003da4273650d6e3b51373e4e86fced975dad607add1184702952d4bf8459d05197293d35b59688a9f13806887f9845211eb2d0b9cc1e089eba8c16f9967d80ec181a754ea6511a897c736ba4c09871d993a41cf7efb08f0479935eaa811865";
    assert_eq!(hex::encode(&digest), expected);
}
