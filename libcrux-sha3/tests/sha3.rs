// Test vectors defined once for reuse across all implementations
mod test_vectors {
    pub const DIGEST_LEN: usize = 42;
    pub const STRING_LEN: usize = DIGEST_LEN * 2;

    pub const DIGEST_LEN_SHAKE128: usize = 168;
    pub const STRING_LEN_SHAKE128: usize = DIGEST_LEN_SHAKE128 * 2;

    pub const DIGEST_LEN_SHAKE256: usize = 136;
    pub const STRING_LEN_SHAKE256: usize = DIGEST_LEN_SHAKE256 * 2;

    pub const EMPTY: &[u8] = b"";
    pub const HELLO: &[u8] = b"Hello, World!";
    pub const STAR0: &[u8] = b"These are not the droids you are looking for.";
    pub const STAR1: &[u8] = b"Help me, Obi-Wan Kenobi, you're my only hope.";
    pub const STAR2: &[u8] = b"I'm one with the Force. The Force is with me.";
    pub const STAR3: &[u8] = b"Your eyes can deceive you. Do not trust them.";

    pub mod sha3_224 {
        pub const HELLO: &str = "853048fb8b11462b6100385633c0cc8dcdc6e2b8e376c28102bc84f2";
        pub const EMPTY: &str = "6b4e03423667dbb73b6e15454f0eb1abd4597f9a1b078e3f5b5a6bc7";
        pub const STAR0: &str = "4d2185f4c559133687b9248f141f0a2b14189dd3e10f63146520bc17";
    }

    pub mod sha3_256 {
        pub const HELLO: &str = "1af17a664e3fa8e419b8ba05c2a173169df76162a5a286e0c405b460d478f7ef";
        pub const EMPTY: &str = "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a";
        pub const STAR0: &str = "f4c623a5f35162ff830afdfea24dfb35ef03a7ef67ff3e35736b9b08ee60401f";
    }

    pub mod sha3_384 {
        pub const HELLO: &str =
            "aa9ad8a49f31d2ddcabbb7010a1566417cff803fef50eba239558826f872e468c5\
                  743e7f026b0a8e5b2d7a1cc465cdbe";
        pub const EMPTY: &str =
            "0c63a75b845e4f7d01107d852e4c2485c51a50aaaa94fc61995e71bbee983a2ac3\
                  713831264adb47fb6bd1e058d5f004";
        pub const STAR0: &str = "b26e8b9b49ed07dcece0359ff5a59c801da66fef6e5bfb\
                  bd9b2a1c9a425fb599778b2cc278d09e2c3d800727f99ed3c5";
    }

    pub mod sha3_512 {
        pub const HELLO: &str =
            "38e05c33d7b067127f217d8c856e554fcff09c9320b8a5979ce2ff5d95dd27ba35\
                  d1fba50c562dfd1d6cc48bc9c5baa4390894418cc942d968f97bcb659419ed";
        pub const EMPTY: &str =
            "a69f73cca23a9ac5c8b567dc185a756e97c982164fe25859e0d1dcc1475c80a615\
                  b2123af1f5f94c11e3e9402c3ac558f500199d95b6d3e301758586281dcd26";
        pub const STAR0: &str =
            "02c3dbe6d722fe92cb8d50be2afbc67c3fda1c34ef69605829ce61398a67a39c92\
                  f5c8f8f2abc026efc977de11418d87e25a7fefff54117d8350701642a9d983";
    }

    pub mod shake128 {
        pub const EMPTY_FIVE_BLOCKS: &str =
            "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef263\
                  cb1eea988004b93103cfb0aeefd2a686e01fa4a58e8a3639ca8a1e3f9ae5\
                  7e235b8cc873c23dc62b8d260169afa2f75ab916a58d974918835d25e6a4\
                  35085b2badfd6dfaac359a5efbb7bcc4b59d538df9a04302e10c8bc1cbf1\
                  a0b3a5120ea17cda7cfad765f5623474d368ccca8af0007cd9f5e4c849f1\
                  67a580b14aabdefaee7eef47cb0fca9767be1fda69419dfb927e9df07348\
                  b196691abaeb580b32def58538b8d23f87732ea63b02b4fa0f4873360e28\
                  41928cd60dd4cee8cc0d4c922a96188d032675c8ac850933c7aff1533b94\
                  c834adbb69c6115bad4692d8619f90b0cdf8a7b9c264029ac185b70b83f2\
                  801f2f4b3f70c593ea3aeeb613a7f1b1de33fd75081f592305f2e4526edc\
                  09631b10958f464d889f31ba010250fda7f1368ec2967fc84ef2ae9aff26\
                  8e0b1700affc6820b523a3d917135f2dff2ee06bfe72b3124721d4a26c04\
                  e53a75e30e73a7a9c4a95d91c55d495e9f51dd0b5e9d83c6d5e8ce803aa6\
                  2b8d654db53d09b8dcff273cdfeb573fad8bcd45578bec2e770d01efde86\
                  e721a3f7c6cce275dabe6e2143f1af18da7efddc4c7b70b5e345db93cc93\
                  6bea323491ccb38a388f546a9ff00dd4e1300b9b2153d2041d205b443e41\
                  b45a653f2a5c4492c1add544512dda2529833462b71a41a45be97290b6f4\
                  cffda2cf990051634a4b1edf6114fb49083c1fa3b302ee097f051266be69\
                  dc716fdeef91b0d4ab2de525550bf80dc8a684bc3b5a4d46b7efae7afdc6\
                  292988dc9acae03f8634486c1abe2781aae4c02f3460d2cd4e6a463a2ba9\
                  562ee623cf0e9f82ab4d0b5c9d040a269366479dff0038abfaf2e0ff21f3\
                  6968972e3f104ddcbe1eb831a87c213162e29b34adfa564d121e9f6e7729\
                  f4203fc5c6c22fa7a7350afddb620923a4a129b8acb19ea10f818c30e3b5\
                  b1c571fa79e57ee304388316a02fcd93a0d8ee02bb85701ee4ff097534b5\
                  02c1b12fbb95c8ccb2f548921d99cc7c9fe17ac991b675e631144423eef7\
                  a5869168da63d1f4c21f650c02923bfd396ca6a5db541068624cbc5ffe20\
                  8c0d1a74e1a29618d0bb60036f5249abfa88898e393718d6efab05bb4127\
                  9efcd4c5a0cc837ccfc22be4f725c081f6aa090749dba7077bae8d4";
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
        pub const STAR0_FIVE_BLOCKS: &str =
            "19a693b556a7aa5b5a239997e20d1c0dae5233837d52030e619d3802af2b7b55d\
                  e2bc9db3830c62ca978ac113a6f7314af6273228a0d4548fa05f3b7c72bd\
                  49aefabdd3589a85d6aebbf4005cfe8deecb80bf339264717a01368ad080\
                  50283faf1e6812ef68568da0881abf55762779b690688b6e80d7e7b023eb\
                  743f7a3ee7fa2ac0a243d379f4f27aacce86527355293d951c60ffbe2931\
                  75ceb60c61dfbbd92d9fb4870b5c3b4abb757de17a4bd004aa36b264e0ef\
                  38f8bd28edb53466276e5c13eec85ad8fc936dc99531fe622d7a4d517e56\
                  7d167cbf2ba78e12a00d7487b81cffa2a4553f93fbf3cbde8a33f357b95b\
                  96a0ff98f303de8aba84afa9bd67f578a4f713e22f226d5d7bb549066b9c\
                  6cf8130c7928e5da1ef2e1713677995a81a9f3daae3dbe5394a4ada0c777\
                  80dd227ba0ad6ee62f23f50e176c594a277c542fcd5a554ad51668d5101c\
                  f9842ce3e8787ac31eeceecb6d6bb9c8abbfe7f670595ffacaeb42650aa3\
                  37a5629aad894ac27b2799c1d591f2270650e42875a177a360cbb70e692e\
                  f35f692abb85e8a637a05ceced3420049e555b42cae2a54dcde2edd84d5e\
                  b38eb2c4fe75b1e70b5a4c7771806f85f8dcdad3a409e9efb6e3eb3cfe11\
                  869ebd9b028c91aeb08a54dad85b155435f85405dbb8b4888469263d4e42\
                  bcf58bf5e3e430dfe26e2873da14a00e8e805aea5f0ecbd5457147c4dae1\
                  a80bc29b0ea326d735176f289419710fe3adfb1b8eb3fa40cc658577a99f\
                  4382bd6b2a5527991ad66d578f596cc559a12f43b928b1006db5fa651ad4\
                  e7c035454238065b95fd5cf24326a78a103075bbffb8ea12c131143c147c\
                  4807160a007aa328936735fa0ef7a6456b92ec6a3ceb2be23904ac8a53c4\
                  bc3064d6724a921d3270dbdb81542ee2d4b005ea0e90a001c929a418976a\
                  4d2285b6f1e2ca8c61e75c55c6801b3ea0a6dee6b91182d98c3068b507cf\
                  1929197a51949234796aefb0d8a19571dc7121275103f390183a3bbf5086\
                  1da01df2b5ba459918580a67653557deae86122e0c88fe0ac68a7d96614e\
                  2f7b6c644cffe83c17ccddcdc3e420cd695d8266eeb3f62e674d3697eefe\
                  1e0c3a380e02a0afb8321280cbf2b9e699ae7c24aa69bd311dbba554e0d3\
                  02e7b0ba906e326c3190d6f48827a1e6970cc74c3b50d6816bd57c3";
        pub const STAR1_FIVE_BLOCKS: &str =
            "df581528bb92ccedd65f004010f1f7a451b6a8268a774d3fa1386ba7a1e34bbf1\
                  2858206a3c288dc6505983a296237593d99230c8a82a63cfab509ed14f43\
                  e01f1cf73d0d015a9cb2d28896b4811c4ec4f27af302791a6c38f14d84d7\
                  512add1044896a52d720cafd156dad5a50bb36d727cca7b531a789e455d8\
                  2cfcef37f4c9c0b1c075b69241f4e65b562912695091eeb2d1b584a4d6ab\
                  ec5b065a19b93882dade4f164424cd6cb5df2d4019936c1f696dc798c3d6\
                  8c02321fe0822b7f0e67960ea8687ef64384efa394a0f027f741900d558c\
                  992bce37c33d7a862ec26ed0e426a3b6716361756403a2f3bdffb46fd38d\
                  43a3e1f46360282020c46767e77e6d10a68501fe22b83e706d20b296c631\
                  24dc7e58de170e3a2c64adab03a7459626a6002f944fd2f2188fc6ce5178\
                  ec76be6bc08bf1a5b50917d3051b6d2bf47b6ddf988b92457fe6ffcffc9b\
                  89541444e29db5d5bdca65b7ab2be2552656b4a24fd2f0360c390b5c4679\
                  395684673467bed7c4579d15ece6a9efa0f8279c48ae247d167a91f6917b\
                  f75ff9860d42c3df95eb47ed2054b01b0dd5fe7dd67444be366afd4ba7e6\
                  61bb585f36f5dca9dd9b960ff89cb267fe180e02f44d2cef19ba86179fe6\
                  f52aa2f43159999ffa24300ae2a56555084ce41e2be54333c067fbd46e30\
                  d9eb23d100c109c6fe2bda954a138c095252e26e3d0e84b220fd8783cf98\
                  82590c94c8b95d38b5a6d1f2e78f3c6d1779fbae33b25fa3664ba7fd6e28\
                  0e8def0954227e325cd561afe82c9ff954108bc938dc80b6bf5b34c2a281\
                  59958f0aff3d6d6a22c10494db62479bccfc24b1cd101120057e2511b9ff\
                  069160cd436383fefcdbe89f25fa45392fbc3799d4eff6c55e7b6e878f38\
                  bf780cf52730e6f22780305e3fa0b330860ed809f349ec4a43e32a87ee20\
                  f1a5bff6493c3889b8386a64be5a57b4dd40b219557c18f4f7329520f3f6\
                  9fd96aeeafc14a33f18330cabba35dacbd1950da366f21a16c0481307c30\
                  f413ff3f74dd7f4da964a0abc735ae941e93df2b73530cf0294fc119a9b9\
                  c9fce592c527927105c4b5a968568ebee831a1d9608e4b10553d57a72c21\
                  3a17cd51c74249004e155691fa6eff8566cd8e2613f4d87e28bbe15268f5\
                  7e90b7675aecc13a2e41d464e9c730be7ccfc76c08280bbe48ca1ef";
        pub const STAR2_FIVE_BLOCKS: &str =
            "c29cd80f81b3aeb4c0e5b4129a036522c5454d71deced3aba0076606681610cf3\
                  8854b19a7ec9210cc6cb59fcd75b0559205d46b111ab07b20c3b6ce3759f\
                  8d4045b4abf95ffc49032d56a05146e41e3f65a3b02c1bab60cfe5fb2bf9\
                  11041a68936fb4bd3f2d39f44198fefc73ecb6a0e56fc6128714d9e197c9\
                  6b0ce83688543bcfd7f2ea231fba0623972ddd0c26b6d2a7daa87828fa94\
                  0a073a7a1ba9b9d811c74122addcd96948ef73dd366cf530eeae11b0f0c9\
                  537450c6517bc9c023a770ce12a53639cb7c90baf1e9ff9f374e0b4c3861\
                  d72672279a62eba15be48233c48407c569ace5cdc9e382d6bb505a973518\
                  6c1d77ffa293d6867a8d46350c3e1cc70ad2ca2aa9e909f34eef998bf7ac\
                  7e15d9bd56c871fc277824d8e2891166b655d1ee043f533e68a9c5a522ca\
                  4488bee3b31bcfa457a89cf5eae981f247772330d5904b31ce59f3e2cd3e\
                  30f01443129ca9870804772a7f01d8c19c0a82fcee6c3581259bfa8e46a0\
                  5e4feaec24330018df95f4c44483c36776b7fc5911fb0eab83689f5f7a15\
                  2f66e80c6116ea1f94a56d5ee5cc90ad93db4eba2b180f458f969a8e70ae\
                  3d61e549371a72df51d6b5bede4bdd75683c1109d5fdef094c661fee5f7d\
                  2ada12d8fc198b982588abe958bea6b6709dde5b4c5003d062972322d51a\
                  7c73be340f68fa747fb4b82777a5d5f5ce271435f60dd4fcaaa8703d5620\
                  6b82d5a174ec2b902290503cbfdb6fed3815522bc7dab52894255f709c88\
                  776b61feb9742d6093e9069a55f86c8dc661c9c731d188d9d8dac3773a1d\
                  83ed0699b6d5beb78409019edc24cbe4a9c09a03aabb6cf582ff96a304c1\
                  232bd288c646ae11361ea492aafc114996aba58da1322c601dd4091f42b8\
                  5672f4911c16e697f388423cf0763c662a617f94b6462a1b4460f85ce0ca\
                  1c0725e7c4c51a6c29d8a9d3e7a79d8a0c98386b9d7dafa22113d5fee527\
                  9525addfd48e5ade7c7aba20f87af1d5c2eb0f9d3b2c9efa6214dc169c90\
                  4b3848d974b7b4ffbd335a0a7246b943c9d4447a308db379697c5344daf7\
                  5e29518ff4994db0a4dc5fe4345c47ba084a0777fd09288b959518182883\
                  e48df76dca7ed15d846fbd751c61c565a2edfd4cee2bdf6ca35eda9fb06e\
                  babc9813c1b43edd4d37acd48bfcb34aad29117dce69b9a8d0cd742";
        pub const STAR3_FIVE_BLOCKS: &str =
            "f3492927232c6971a800ad2d884b09fbe3c0debcaab1d2840251565d48a705610\
                  65f05948f18438f36de4c027d9dfc0b6884bc3b79a28a99e05d3b7fa1357\
                  d21b01d026fa3efc1c54c08ba0857ea89d4447de66bda1fd62c6f98b76cd\
                  7be67cd11efb4db3eef8cb89a714d9ffbe9c10a7ee8f3ef3c62e87b343d2\
                  2daf51388dca6b8bdb9ea3f7b647ddff9f94d1b17ea898acca59ac8318f6\
                  82042c107c76dbb9f4b1df4624203bc65017acde3a3214956214d5b31c0e\
                  35c7cfe096c55714cd2d6c14683eeec873a5a54608153cc1ed9b893ca2ab\
                  4aa4ddd242c7f544e912897f350cc5e18e465d9216ccbe25061cde0f2010\
                  fa97318d19ed42b002b4891fbe226865c5408ac1e045d76b3a8d89e36f1e\
                  0d8ea97ea99cd45a000175ffca9e9c616696a0209b0862f6a51ec3a9b274\
                  ea4943456c2cfa1b07de6dfa8bfdf8c8e53603137723259be354afec1954\
                  de69a183eaa10e2a65e4eb7c25ac170938e430696e2b76421c5e2baf3caf\
                  913feadaeaacf13192cd87f400f4d632bd6864d9245af8395d4482f30b49\
                  f7d62b29bf26873c7851d020b64c9426400a3a9129bf737737223b990110\
                  444b96fac1a4ffeeec9f054f572de03629912bc3cb96217f8a93f43784f4\
                  c144d89ea9f4db2916f165cf503195b8dca389b963d89da1ff6acb9ee56f\
                  e463f2f8932986a365ac49d1400027e6dbc73ce97890524413125c12ad5b\
                  913f5d81bad9e8582f4c05cbb190d09d63b7a63885ba9765fc931e4892e3\
                  86a6c4ad6f935aaf777fe0585f6465be08099aaccac3dad80adbd85ade27\
                  110ed67a91f483cc03dffbc3cf36c2139d4ecd04a0bd88f824c574b8092c\
                  711ca5e8f2ceb27706964c43921f352b36ead0ad19f9f5640ece403719da\
                  06ba91f3cef532d49dab2747322dec58ce8b9a938aa2f0e5d4b7c198cae4\
                  de6cd77a211cef8a29f220c0e792aeb6e601f5de502444fcd143cb72a700\
                  3239333d2c82f357e35a51adeb6fe40cf913b55e2a2bd2256efafcc2229a\
                  8a39668a9f78ab445f6a0853919c60aba3c750ba2d8195b9c052ac2457f1\
                  eefbf49a28995a7eaee8061ea05e689f80593dc36c1f7e62a113dd754a1f\
                  e4e062257ff5906e73c6f8499a1470faa07584003ef887d3fb834019c3dc\
                  1de58a9344fb67806f360aec9a9a6640f8301abbf043d5c6d922bdb";
    }

    pub mod shake256 {
        pub const EMPTY_FIVE_BLOCKS: &str =
            "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762fd\
                  75dc4ddd8c0f200cb05019d67b592f6fc821c49479ab48640292eacb3b7c\
                  4be141e96616fb13957692cc7edd0b45ae3dc07223c8e92937bef84bc0ea\
                  b862853349ec75546f58fb7c2775c38462c5010d846c185c15111e595522\
                  a6bcd16cf86f3d122109e3b1fdd943b6aec468a2d621a7c06c6a957c62b5\
                  4dafc3be87567d677231395f6147293b68ceab7a9e0c58d864e8efde4e1b\
                  9a46cbe854713672f5caaae314ed9083dab4b099f8e300f01b8650f1f4b1\
                  d8fcf3f3cb53fb8e9eb2ea203bdc970f50ae55428a91f7f53ac266b28419\
                  c3778a15fd248d339ede785fb7f5a1aaa96d313eacc890936c173cdcd0fa\
                  b882c45755feb3aed96d477ff96390bf9a66d1368b208e21f7c10d04a3db\
                  d4e360633e5db4b602601c14cea737db3dcf722632cc77851cbdde2aaf0a\
                  33a07b373445df490cc8fc1e4160ff118378f11f0477de055a81a9eda57a\
                  4a2cfb0c83929d310912f729ec6cfa36c6ac6a75837143045d791cc85eff\
                  5b21932f23861bcf23a52b5da67eaf7baae0f5fb1369db78f3ac45f8c4ac\
                  5671d85735cdddb09d2b1e34a1fc066ff4a162cb263d6541274ae2fcc865\
                  f618abe27c124cd8b074ccd516301b91875824d09958f341ef274bdab0ba\
                  e316339894304e35877b0c28a9b1fd166c796b9cc258a064a8f57e27f2a5\
                  b8d548a728c9444ecb879adc19de0c1b8587de3e73e15d3ce2db7c9fa7b5\
                  8ffc0e87251773faf3e8f3e3cf1d4dfa723afd4da9097cb3c866acbefab2\
                  c4e85e1918990ff93e0656b5f75b08729c60e6a9d7352b9efd2e33e3d1ba\
                  6e6d89edfa671266ece6be7bb5ac948b737e41590abe138ce1869c086801\
                  62f08863d174e77e07a9ddb33b57de04c443a5bd77c42036871aae789336\
                  2b27015b84b4139f0e313579b4ef5f6b642";
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
        pub const STAR0_FIVE_BLOCKS: &str =
            "318b90eacc9b56ffc4d3d6c4fe4983ff1e42c294c7b7df777b631956cfb5f2dce\
                  b839182800ff60b0cc2df9e282860abdae32c9e1c71cd1cf6b753b1e3edb\
                  f181a9e7503bb92de170a9656c164801e985099c69bf70dc24d1aa405719\
                  f9389584759754297877c18254c431db55de8310adb892cf3ca1f08eaf1d\
                  eeb3cc97c1e25841e03e83a0b71686cc4fc828f14cea4b80906aa0138aaf\
                  febb5c179fa68b96ea4249f442b6689a7736d1e888602aced180b23405f0\
                  d5c5a859485769f5e22d00496672f5dedd6f8a5d68d209020c127021e8a1\
                  b8b98dfe88e8407724702dd42576fc57404d54fc3ef3149225a9487ec1c6\
                  d0e73dc15787a0fef9fde69f3f7416aec6942cc3a78ad17967d3eb607fb0\
                  c55579cb3f88f8cefdeb45ba2d0b31f5986a89f5ac1eaf762e7092625251\
                  28f5b6cc29e382a8e22afad105fd6d7cc407868d5aeb71eae736fb2a1974\
                  a1d185e9faf57c237bd8cf76ad86ceb36626fdef09ab79c700aa5bf0bbaf\
                  b715903ee99b37e8c82061c6c40a4817208c1eb457b2d9972240b7e70853\
                  cfab815594ab5118cb31edc61d1d632a9524f6a43fc2fc72a8c0402ce51c\
                  9acbcba25acae9f66eff30d865c493c6be716fbe130e17b774ae9d8bc67d\
                  2eb9fd2f71c9f896b68a25fd09bcd8074353286b7878418c8a7d2a0a9a2b\
                  bb219120cf35ab38059670b300a0a4b79be03b37974641b22e51198657d2\
                  7641b685952064d16efc2e70752f2fc882b108e0a23bfbd1dffafbbf5701\
                  d801b0e1c5788e60646ed82a045ee5c843111e73863e8cd644f49b93b6aa\
                  39621bbe7ed44179707e146440926bca29226db5bee9d986f4cd564cd5a2\
                  f2948d56792b1a17a8fea43d60bb81d31020d6a37b52b5f00bb164ccd0c0\
                  e7d32d74816ebace533f5ef6eb44b621a9352862ae55f8d6924f2923a4a2\
                  57a4f0430584b8b029fac9e675116589513";
        pub const STAR1_FIVE_BLOCKS: &str =
            "0db781f9947f25f99279c4791df0fdbcd3d54a08420e49157621ac1bdab9fc0a2\
                  b822ceb1babf425d6d20607ce46981c843a48802e38f4225b3bb884c0b35\
                  4a7fd1261817e4decbb08fe2d4b21853380a7b30dfad8141631dfb966fb4\
                  4f1de4489ad23ea2a35d3b70ecd6b0244cb834edc5039194223216b5d49f\
                  285f856b9b4e4b32862505f77bdf2b21b9c71efcf39b2d3d6f462a0652c7\
                  38785cfffa01ee666978e75e28394ff19d027e7b71bb9492c61ac55dc7aa\
                  3a2a114284e7109ee46cde2d12d37ed07c41a52d8bfb88625749aa117e63\
                  4c4a994d4fe268b68a867a2fa7a74306d1e0aa88f5b4a71e89abded07b91\
                  3bdab8c4739668ace2f08b2f1ca81d0793a63c1d0baa001bc48fee80d22e\
                  d1e61dc4b4cbfc65af9bee15f44566fb3768e3d93504307a6d575f68baea\
                  cde755486e0d845251e1f5bf55fdc261a2587ad8ba03c0f1d9856518603c\
                  d4becab476c0492b99466c35b51be6cebb042d5edf4361ad95f4a121a687\
                  79489b19895a02a98e646764dab38d577cb0debe15c1a1ddee9407e35c19\
                  b431c31cb413c33dba06868311c074f5ed908291310bfa82d8456c352c76\
                  ba1d72ade5551e8444afddace57af209a5b84209cdcfe7bf8e04f5471a60\
                  403324144e26c41acf8d05efac88de942c2742ca92af1e7dcb901ec07470\
                  f9cfcd2359abcd760d0fdacac0cbc19299d6ea444ad571cfe393051f314d\
                  dcfdbbfae1239f3f6aed0b30654bf1893a9c2a3461239d0b6052f620c59f\
                  f2b554f6a719f56089d630b373080a2590375074c4612f809df6f84923a2\
                  12638057dcd7bf7cceb504715133f95bd314db7175b2487ea787647fed93\
                  ce85c5cfc9eef0c2b8df59d4e317fcad14a2eae0e7df407f1b609ec42fa8\
                  230c99ed2568f3fbd7aac8951c7b1a7bcdb4b8a4959031881471486e9605\
                  5aa983b179dafaac32288ffe5bf7ac6fea6";
        pub const STAR2_FIVE_BLOCKS: &str =
            "923fa368ea69e2216539b4fb3c40510c4442df74e5ebb6539b6e35ac14554895a\
                  e24788b1ef9af26fd0f94ac68685964cc2c7702905875822b6606eba694b\
                  193640a48b067d6d8f3d227aad54cbe213ecdfbcdd65b60d06ae386b09c0\
                  1ea4690df289553b366f7c018c3064989f0062e2e0648018cd249bbe6bc7\
                  cc0b8a7544874349d68eb676bc9266392c63aebb5c8ee316feff8278679a\
                  2a5e5f974042a962129feb7456430736b4ddd0345b124119c1b016787a53\
                  424125234f76d08d4ad41666f457a5e752b94b765af5991464a01035719d\
                  638bf2d87463675d5010e4c124dad36c9dba24a2ca210d952932bc51d02d\
                  3b2fefa4cfbdcc6c0fac5e2d1a9e4aa79a9651913caab7a35ecfbe11acf3\
                  08edf1d2aa95e00c7b39496f0e4c6d0b13d67e2e8f8ae4c9db766c4ea725\
                  8fae0c9c4be1dcd4e6eb6cd9f463967ca9c57f349774eee8f82bbbd87179\
                  11e4e61618117c278fbe48018049946b764060cd7e3c0618c736a907c4f4\
                  9d23abdc90743c9b665be7ffaf14ba66a32f5395b6ea5b762a608012b7e1\
                  594f8502ef23760d07927b373d998e030e6a45ac574b388e6ce55d30444b\
                  ce1423bea6bfaf966880a77a4c0a57f480ef22c899d99b3acdeb64b9dc1d\
                  5db2966b711156807274e740aa5cd63afef9bf2d4cd8b549dd2e0dc5dc72\
                  a5e01a0afc4114f4664e5e6e4b0cd33f1eee947523f3348c37cd972ac82e\
                  d1d01ddc405905d76191e9fd25b094bb00d80d59225db64faf8c2116ca6b\
                  09fc37886e631a839e86a560557d8627bf9b45f07c6cd4b35b51af6f458a\
                  57867458e4fdb832867ad07202ff9e27ca2b2442ce0b187314af1a28da55\
                  75c5021b6cd7c209f505e28257ab95c4a9d9a1143da55970e21c59114a2a\
                  8037536084268e98cde407b40687714efcd20b74d979b294d2d9e27c3e37\
                  2bdaa61a3021877812ab3e72ffe69218f12";
        pub const STAR3_FIVE_BLOCKS: &str =
            "ad44291b72b13bfca19317a6d9000f6ce447e8f3fc11e1ec58ce692700dbaaf24\
                  d2601b8f59f750814d4787b52844678272c25fb8dff279ddf8a86b201cf1\
                  4eac0bac2db6cc7d42d758c1789951ed1ce5a8dbde26bcd8cf31111f81e3\
                  78d61b9f0e398abf895695e46ba58642a23e3cf68bf77c05f2e30ca762a4\
                  af5ba72e201d00f3c554031ede2ce0c2dd4965b5c19d624bd4fe30d682eb\
                  0a0ae5a3f7329af25331201ade493cbfdb5c45ff96c5c232d36eefa0a11b\
                  05d6fdc820365f7d55706cd2177ff618628d6e7eab3607b448bb8e3021a6\
                  14f4721715895c8692bf3bc5f35457bc29c3e81b7fafb7be54caa5c7f78b\
                  4e6839a38230d26c33d3132ace47b1b661458a72615e45fd033a92699a1d\
                  5afb6e9c43ba4877a4c9f7fb2ea38b2d0fc69ca64f92cfcce16ca2484ee5\
                  9e5033008873002227b9f9d9cd43b3b4f2d3a5864dfd7af97dd8340fe850\
                  c4d85b3f0c7c9babafc62278e82c98b45f1dda817e8f79a5b487afaf63fe\
                  9b33430ac4c82c16125a6e056ece18db19fad08c747db0cca38afbee40f9\
                  bdd0e223f0dbadd6cfe27b2be04aa82dbed7517fec6e13121d314087c068\
                  0f9d025a223a687dc3327c5a97ee0a5d9494e0701b059c3cfbebe7f34602\
                  3bcc70a6209ce5b830020b88614ae4899fbe6abcf79259f32777980e27ea\
                  0a9d97a47cac2fe6c4965f2abc0f54ffbda78ccee5dff773572034547642\
                  3086ab3b9be107f824619d3fe702492fe18e48c6bdbc212fab0d9b76a69f\
                  53c77776c5818bd08f5632cd03236595a0c1f9f2b8df52a8f7058e1d6dfa\
                  80cc3d1bd4e59968f33dceb9e0d286cf0c83ede2a7e52d33a3b891e73b4a\
                  b558ed01956b689d0e53b9c19f9d0a7f6d13c291cd9f34f21b9cb193c242\
                  51224ee93a452e5728f44735af4293f43a62720771ab127f026ec08e74a0\
                  7351335e5fff8e14e54c4cb027282bed13e";
    }
}

// Portable implementation tests
// #[cfg(not(any(feature = "simd128", feature = "simd256")))]
mod portable {
    use super::test_vectors;
    use super::test_vectors::{DIGEST_LEN, DIGEST_LEN_SHAKE256, STRING_LEN, STRING_LEN_SHAKE256};
    use libcrux_sha3::portable::incremental::Xof;
    use libcrux_sha3::portable::{incremental, sha224, sha256, sha384, sha512, shake128, shake256};

    #[test]
    fn sha3_224() {
        let mut digest = [0u8; 28];

        sha224(&mut digest, test_vectors::EMPTY);
        assert_eq!(hex::encode(digest), test_vectors::sha3_224::EMPTY);

        sha224(&mut digest, test_vectors::HELLO);
        assert_eq!(hex::encode(digest), test_vectors::sha3_224::HELLO);

        sha224(&mut digest, test_vectors::STAR0);
        assert_eq!(hex::encode(digest), test_vectors::sha3_224::STAR0);
    }

    #[test]
    fn sha3_256() {
        let mut digest = [0u8; 32];

        sha256(&mut digest, test_vectors::EMPTY);
        assert_eq!(hex::encode(digest), test_vectors::sha3_256::EMPTY);

        sha256(&mut digest, test_vectors::HELLO);
        assert_eq!(hex::encode(digest), test_vectors::sha3_256::HELLO);

        sha256(&mut digest, test_vectors::STAR0);
        assert_eq!(hex::encode(digest), test_vectors::sha3_256::STAR0);
    }

    #[test]
    fn sha3_384() {
        let mut digest = [0u8; 48];

        sha384(&mut digest, test_vectors::EMPTY);
        assert_eq!(hex::encode(digest), test_vectors::sha3_384::EMPTY);

        sha384(&mut digest, test_vectors::HELLO);
        assert_eq!(hex::encode(digest), test_vectors::sha3_384::HELLO);

        sha384(&mut digest, test_vectors::STAR0);
        assert_eq!(hex::encode(digest), test_vectors::sha3_384::STAR0);
    }

    #[test]
    fn sha3_512() {
        let mut digest = [0u8; 64];

        sha512(&mut digest, test_vectors::EMPTY);
        assert_eq!(hex::encode(digest), test_vectors::sha3_512::EMPTY);

        sha512(&mut digest, test_vectors::HELLO);
        assert_eq!(hex::encode(digest), test_vectors::sha3_512::HELLO);

        sha512(&mut digest, test_vectors::STAR0);
        assert_eq!(hex::encode(digest), test_vectors::sha3_512::STAR0);
    }

    #[test]
    fn sha3_shake128() {
        let mut digest = [0u8; DIGEST_LEN];

        shake128(&mut digest, test_vectors::EMPTY);
        assert_eq!(
            hex::encode(digest),
            &test_vectors::shake128::EMPTY_FIVE_BLOCKS[..STRING_LEN]
        );

        shake128(&mut digest, test_vectors::HELLO);
        assert_eq!(
            hex::encode(digest),
            &test_vectors::shake128::HELLO_FIVE_BLOCKS[..STRING_LEN]
        );
        let mut digest = [0u8; 53];

        shake128(&mut digest, test_vectors::STAR0);
        assert_eq!(
            hex::encode(digest),
            test_vectors::shake128::STAR0_FIVE_BLOCKS[..53 * 2]
        );
    }

    #[test]
    fn sha3_shake256() {
        let mut digest = [0u8; DIGEST_LEN];

        shake256(&mut digest, test_vectors::EMPTY);
        assert_eq!(
            hex::encode(digest),
            &test_vectors::shake256::EMPTY_FIVE_BLOCKS[..STRING_LEN]
        );

        shake256(&mut digest, test_vectors::HELLO);
        assert_eq!(
            hex::encode(digest),
            &test_vectors::shake256::HELLO_FIVE_BLOCKS[..STRING_LEN]
        );

        let mut digest = [0u8; 71];

        shake256(&mut digest, test_vectors::STAR0);
        assert_eq!(
            hex::encode(digest),
            test_vectors::shake256::STAR0_FIVE_BLOCKS[..71 * 2]
        );
    }

    #[test]
    fn sha3_shake128_incremental() {
        // Test squeezing 1 block (168 bytes)
        let mut state = incremental::shake128_init();
        incremental::shake128_absorb_final(&mut state, test_vectors::HELLO);

        // Test squeezing next block (168 bytes)
        let mut digest = [0u8; DIGEST_LEN * 4];
        incremental::shake128_squeeze_next_block(&mut state, &mut digest);
        assert_eq!(
            hex::encode(digest),
            &test_vectors::shake128::HELLO_FIVE_BLOCKS[336..672]
        );

        // ---

        // Test squeezing 3 blocks (504 bytes)
        state = incremental::shake128_init();
        incremental::shake128_absorb_final(&mut state, test_vectors::HELLO);

        let mut digest = [0u8; DIGEST_LEN * 12];
        incremental::shake128_squeeze_first_three_blocks(&mut state, &mut digest);
        assert_eq!(
            hex::encode(digest),
            &test_vectors::shake128::HELLO_FIVE_BLOCKS[..STRING_LEN * 12]
        );

        // ---

        // Test squeezing 5 blocks (840 bytes)
        state = incremental::shake128_init();
        incremental::shake128_absorb_final(&mut state, test_vectors::HELLO);

        let mut digest = [0u8; DIGEST_LEN * 20];
        incremental::shake128_squeeze_first_five_blocks(&mut state, &mut digest);
        assert_eq!(
            hex::encode(digest),
            test_vectors::shake128::HELLO_FIVE_BLOCKS
        );
    }

    #[test]
    fn sha3_shake256_incremental() {
        // Test squeezing 1 block (136 bytes for SHAKE256, not 168)
        let mut state = incremental::shake256_init();
        incremental::shake256_absorb_final(&mut state, test_vectors::HELLO);

        let mut digest = [0u8; DIGEST_LEN_SHAKE256];
        incremental::shake256_squeeze_first_block(&mut state, &mut digest);
        assert_eq!(
            hex::encode(digest),
            &test_vectors::shake256::HELLO_FIVE_BLOCKS[..STRING_LEN_SHAKE256]
        );

        // Test squeezing next block (136 bytes)
        incremental::shake256_squeeze_next_block(&mut state, &mut digest);
        assert_eq!(
            hex::encode(digest),
            &test_vectors::shake256::HELLO_FIVE_BLOCKS
                [DIGEST_LEN_SHAKE256 * 2..DIGEST_LEN_SHAKE256 * 4]
        );
    }

    #[test]
    fn sha3_shake128_absorb() {
        let mut state = incremental::Shake128Xof::new();
        state.absorb_final(b"Hello, ");

        let mut digest = [0u8; 32];
        state.squeeze(&mut digest);
        let expected = "62dac7f538d3c56e66a1e0ccda69f4b6c8f6269572ad9312c7a04a2228b474a5";
        assert_eq!(hex::encode(digest), expected);

        // ---

        state = incremental::Shake128Xof::new();
        state.absorb(b"Hello, ");
        state.absorb_final(b"World!");

        state.squeeze(&mut digest);
        assert_eq!(
            hex::encode(digest),
            &test_vectors::shake128::HELLO_FIVE_BLOCKS[..64]
        );

        // ---

        state = incremental::Shake128Xof::new();
        state.absorb(b"Hello, ");
        state.absorb_final(&[]);

        state.squeeze(&mut digest);
        assert_eq!(hex::encode(digest), expected);
    }

    #[test]
    fn sha3_shake256_absorb() {
        let mut state = incremental::Shake256Xof::new();
        state.absorb_final(b"Hello, ");

        let mut digest = [0u8; 32];
        state.squeeze(&mut digest);
        let expected = "018680a686f24f889fe4613dba0058ea1b035b7270a8c26b363f42557bbd991a";
        assert_eq!(hex::encode(digest), expected);

        // ---

        state = incremental::Shake256Xof::new();
        state.absorb(b"Hello, ");
        state.absorb_final(b"World!");

        state.squeeze(&mut digest);
        assert_eq!(
            hex::encode(digest),
            &test_vectors::shake256::HELLO_FIVE_BLOCKS[..64]
        );

        // ---

        state = incremental::Shake256Xof::new();
        state.absorb(b"Hello, ");
        state.absorb_final(&[]);

        state.squeeze(&mut digest);
        assert_eq!(hex::encode(digest), expected);
    }
}

#[cfg(feature = "simd256")]
mod simd256 {
    use super::test_vectors::{
        self, DIGEST_LEN_SHAKE128, DIGEST_LEN_SHAKE256, STRING_LEN_SHAKE128, STRING_LEN_SHAKE256,
    };
    use libcrux_sha3::avx2::x4::incremental;

    #[test]
    fn sha3_shake128_squeeze_first_three_next_block() {
        let mut state = incremental::init();

        incremental::shake128_absorb_final(
            &mut state,
            test_vectors::STAR0,
            test_vectors::STAR1,
            test_vectors::STAR2,
            test_vectors::STAR3,
        );

        let mut out0 = [0u8; DIGEST_LEN_SHAKE128 * 3];
        let mut out1 = [0u8; DIGEST_LEN_SHAKE128 * 3];
        let mut out2 = [0u8; DIGEST_LEN_SHAKE128 * 3];
        let mut out3 = [0u8; DIGEST_LEN_SHAKE128 * 3];

        incremental::shake128_squeeze_first_three_blocks(
            &mut state, &mut out0, &mut out1, &mut out2, &mut out3,
        );

        assert_eq!(
            hex::encode(&out0),
            test_vectors::shake128::STAR0_FIVE_BLOCKS[..STRING_LEN_SHAKE128 * 3]
        );
        assert_eq!(
            hex::encode(&out1),
            test_vectors::shake128::STAR1_FIVE_BLOCKS[..STRING_LEN_SHAKE128 * 3]
        );
        assert_eq!(
            hex::encode(&out2),
            test_vectors::shake128::STAR2_FIVE_BLOCKS[..STRING_LEN_SHAKE128 * 3]
        );
        assert_eq!(
            hex::encode(&out3),
            test_vectors::shake128::STAR3_FIVE_BLOCKS[..STRING_LEN_SHAKE128 * 3]
        );

        let mut out0 = [0u8; DIGEST_LEN_SHAKE128];
        let mut out1 = [0u8; DIGEST_LEN_SHAKE128];
        let mut out2 = [0u8; DIGEST_LEN_SHAKE128];
        let mut out3 = [0u8; DIGEST_LEN_SHAKE128];

        incremental::shake128_squeeze_next_block(
            &mut state, &mut out0, &mut out1, &mut out2, &mut out3,
        );

        assert_eq!(
            hex::encode(&out0),
            test_vectors::shake128::STAR0_FIVE_BLOCKS
                [STRING_LEN_SHAKE128 * 3..STRING_LEN_SHAKE128 * 4]
        );
        assert_eq!(
            hex::encode(&out1),
            test_vectors::shake128::STAR1_FIVE_BLOCKS
                [STRING_LEN_SHAKE128 * 3..STRING_LEN_SHAKE128 * 4]
        );
        assert_eq!(
            hex::encode(&out2),
            test_vectors::shake128::STAR2_FIVE_BLOCKS
                [STRING_LEN_SHAKE128 * 3..STRING_LEN_SHAKE128 * 4]
        );
        assert_eq!(
            hex::encode(&out3),
            test_vectors::shake128::STAR3_FIVE_BLOCKS
                [STRING_LEN_SHAKE128 * 3..STRING_LEN_SHAKE128 * 4]
        );
    }

    #[test]
    fn sha3_shake128_squeeze_first_five() {
        let mut state = incremental::init();

        incremental::shake128_absorb_final(
            &mut state,
            test_vectors::STAR0,
            test_vectors::STAR1,
            test_vectors::STAR2,
            test_vectors::STAR3,
        );

        let mut out0 = [0u8; DIGEST_LEN_SHAKE128 * 5];
        let mut out1 = [0u8; DIGEST_LEN_SHAKE128 * 5];
        let mut out2 = [0u8; DIGEST_LEN_SHAKE128 * 5];
        let mut out3 = [0u8; DIGEST_LEN_SHAKE128 * 5];

        incremental::shake128_squeeze_first_five_blocks(
            &mut state, &mut out0, &mut out1, &mut out2, &mut out3,
        );

        assert_eq!(
            hex::encode(&out0),
            test_vectors::shake128::STAR0_FIVE_BLOCKS
        );
        assert_eq!(
            hex::encode(&out1),
            test_vectors::shake128::STAR1_FIVE_BLOCKS
        );
        assert_eq!(
            hex::encode(&out2),
            test_vectors::shake128::STAR2_FIVE_BLOCKS
        );
        assert_eq!(
            hex::encode(&out3),
            test_vectors::shake128::STAR3_FIVE_BLOCKS
        );
    }

    #[test]
    fn sha3_shake256_squeeze_first_next() {
        let mut state = incremental::init();

        incremental::shake256_absorb_final(
            &mut state,
            test_vectors::STAR0,
            test_vectors::STAR1,
            test_vectors::STAR2,
            test_vectors::STAR3,
        );

        let mut out0 = [0u8; DIGEST_LEN_SHAKE256];
        let mut out1 = [0u8; DIGEST_LEN_SHAKE256];
        let mut out2 = [0u8; DIGEST_LEN_SHAKE256];
        let mut out3 = [0u8; DIGEST_LEN_SHAKE256];

        incremental::shake256_squeeze_first_block(
            &mut state, &mut out0, &mut out1, &mut out2, &mut out3,
        );

        assert_eq!(
            hex::encode(&out0),
            test_vectors::shake256::STAR0_FIVE_BLOCKS[..STRING_LEN_SHAKE256]
        );
        assert_eq!(
            hex::encode(&out1),
            test_vectors::shake256::STAR1_FIVE_BLOCKS[..STRING_LEN_SHAKE256]
        );
        assert_eq!(
            hex::encode(&out2),
            test_vectors::shake256::STAR2_FIVE_BLOCKS[..STRING_LEN_SHAKE256]
        );
        assert_eq!(
            hex::encode(&out3),
            test_vectors::shake256::STAR3_FIVE_BLOCKS[..STRING_LEN_SHAKE256]
        );

        incremental::shake256_squeeze_next_block(
            &mut state, &mut out0, &mut out1, &mut out2, &mut out3,
        );

        assert_eq!(
            hex::encode(&out0),
            test_vectors::shake256::STAR0_FIVE_BLOCKS[STRING_LEN_SHAKE256..STRING_LEN_SHAKE256 * 2]
        );
        assert_eq!(
            hex::encode(&out1),
            test_vectors::shake256::STAR1_FIVE_BLOCKS[STRING_LEN_SHAKE256..STRING_LEN_SHAKE256 * 2]
        );
        assert_eq!(
            hex::encode(&out2),
            test_vectors::shake256::STAR2_FIVE_BLOCKS[STRING_LEN_SHAKE256..STRING_LEN_SHAKE256 * 2]
        );
        assert_eq!(
            hex::encode(&out3),
            test_vectors::shake256::STAR3_FIVE_BLOCKS[STRING_LEN_SHAKE256..STRING_LEN_SHAKE256 * 2]
        );

        incremental::shake256_squeeze_next_block(
            &mut state, &mut out0, &mut out1, &mut out2, &mut out3,
        );

        assert_eq!(
            hex::encode(&out0),
            test_vectors::shake256::STAR0_FIVE_BLOCKS
                [STRING_LEN_SHAKE256 * 2..STRING_LEN_SHAKE256 * 3]
        );
        assert_eq!(
            hex::encode(&out1),
            test_vectors::shake256::STAR1_FIVE_BLOCKS
                [STRING_LEN_SHAKE256 * 2..STRING_LEN_SHAKE256 * 3]
        );
        assert_eq!(
            hex::encode(&out2),
            test_vectors::shake256::STAR2_FIVE_BLOCKS
                [STRING_LEN_SHAKE256 * 2..STRING_LEN_SHAKE256 * 3]
        );
        assert_eq!(
            hex::encode(&out3),
            test_vectors::shake256::STAR3_FIVE_BLOCKS
                [STRING_LEN_SHAKE256 * 2..STRING_LEN_SHAKE256 * 3]
        );
    }
}

#[cfg(feature = "simd128")]
mod simd128 {
    use super::*;
    use libcrux_sha3::neon::x2::incremental::{
        init, shake256_absorb_final, shake256_squeeze_first_block,
    };

    const DIGEST_LEN_SHAKE256: usize = 136;
    const STRING_LEN_SHAKE256: usize = DIGEST_LEN_SHAKE256 * 2;

    #[test]
    fn sha3_shake256_incremental() {
        // Test squeezing 1 block (136 bytes for SHAKE256, not 168)
        let mut state = init();
        shake256_absorb_final(&mut state, test_vectors::HELLO, test_vectors::HELLO);

        let mut digest0 = [0u8; DIGEST_LEN_SHAKE256];
        let mut digest1 = [0u8; DIGEST_LEN_SHAKE256];
        shake256_squeeze_first_block(&mut state, &mut digest0, &mut digest1);

        assert_eq!(hex::encode(digest0), hex::encode(digest1),);
        assert_eq!(
            hex::encode(digest0),
            &test_vectors::shake256::HELLO_FIVE_BLOCKS[..STRING_LEN_SHAKE256]
        );
    }
}
