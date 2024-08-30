pub mod util {
    pub fn randombytes(n: usize) -> Vec<u8> {
        use rand::rngs::OsRng;
        use rand::RngCore;

        let mut bytes = vec![0u8; n];
        OsRng.fill_bytes(&mut bytes);
        bytes
    }

    pub fn fmt(x: usize) -> String {
        let base = (x as f64).log(1024f64).floor() as usize;
        let suffix = ["", "KB", "MB", "GB"];
        format!("{} {}", x >> (10 * base), suffix[base])
    }
}
