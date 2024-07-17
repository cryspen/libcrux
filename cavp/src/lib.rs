use std::{
    fs::File,
    io::{BufRead, BufReader},
};

/// Errors
#[derive(Debug, Clone, Copy)]
pub enum Error {
    FileOpen,
    Read,
}

/// The test vector representation in the file
struct HashTv {}

impl HashTv {
    fn read(mut reader: impl BufRead) -> Result<TestVector, Error> {
        let mut tv = TestVector::default();

        let mut test = Sha3Test::default();

        // Read a single entry
        loop {
            let mut line = String::new();
            let bytes_read = reader.read_line(&mut line).map_err(|_| Error::Read)?;
            if bytes_read == 0 {
                return Ok(tv);
            }

            let mut line = line.trim();

            // Filter out empty lines and comments
            if line.len() == 0 || line.starts_with("#") {
                continue;
            }
            log::debug!("reading {}", line);

            // Read a section header
            //
            // A section header has the form `[ ... ]`
            if line.starts_with("[") && line.ends_with("]") {
                line = line.strip_suffix("]").ok_or(Error::Read)?;
                line = line.strip_prefix("[").ok_or(Error::Read)?;
                log::debug!("line {line}");
                tv.out_len = read_kv_type(line, "L")?.value;
                test = Sha3Test::default();

                // Continue with the next line
                continue;
            }

            // Read a test case
            //
            // A test case has the form
            // ```
            // ... = ...
            //
            // ```
            let mut key_value = line.split("=");
            let key = key_value.next().map(|v| v.trim());
            log::debug!("key: {key:?}");
            match key {
                Some("Len") => {
                    test.length = to_usize(key_value)?;
                }
                Some("Msg") => {
                    test.msg = to_bytes(key_value)?;
                }
                Some("MD") => {
                    test.digest = to_bytes(key_value)?;
                    tv.tests.push(test.clone());

                    // This is the last value
                    continue;
                }
                _ => return Err(Error::Read),
            }
        }
    }
}

trait FromStr {
    fn from_str(s: &str) -> Result<Self, Error>
    where
        Self: Sized;
}

impl FromStr for usize {
    fn from_str(s: &str) -> Result<Self, Error> {
        s.parse().map_err(|_| Error::Read)
    }
}

impl FromStr for Vec<u8> {
    fn from_str(s: &str) -> Result<Self, Error> {
        hex::decode(s).map_err(|_| Error::Read)
    }
}

/// A key-value pair
///
/// This is represented as `key = value` in the rsp file with `value: T`
struct KeyValue<T: FromStr> {
    key: String,
    value: T,
}

impl<T: FromStr> KeyValue<T> {
    fn new(key: String, value: T) -> Self {
        Self { key, value }
    }
}

/// Read key value pair
fn read_kv_string<T: FromStr>(kv: &str) -> Result<KeyValue<T>, Error> {
    let mut key_value = kv.split("=");
    let key = key_value.next().map(|v| v.trim()).ok_or(Error::Read)?;
    log::debug!("key: {key:?}");
    let value = key_value.next().map(|v| v.trim()).ok_or(Error::Read)?;
    log::debug!("value: {value:?}");
    Ok(KeyValue::new(key.to_string(), T::from_str(value)?))
}

/// Read key value pair with type
fn read_kv_type<T: FromStr>(kv: &str, key: &str) -> Result<KeyValue<T>, Error> {
    let kv = read_kv_string(kv)?;
    if kv.key != key {
        log::error!("Expected key {key} but got {}", kv.key);
        return Err(Error::Read);
    }
    Ok(kv)
}

/// Helper to convert strings to bytes
fn to_bytes(mut value: std::str::Split<&str>) -> Result<Vec<u8>, Error> {
    let next = value.next().map(|v| v.trim());
    log::debug!("value: {next:?}");
    Ok(hex::decode(next.ok_or(Error::Read)?).map_err(|_| Error::Read)?)
}

/// Helper to convert strings to usize
fn to_usize(mut value: std::str::Split<&str>) -> Result<usize, Error> {
    let next = value.next().map(|v| v.trim());
    log::debug!("value: {next:?}");
    Ok(next.map(|v| v.parse().ok()).flatten().ok_or(Error::Read)?)
}

/// A SHA3 test.
#[derive(Debug, Clone, Default)]
pub struct Sha3Test {
    pub length: usize,
    pub msg: Vec<u8>,
    pub digest: Vec<u8>,
}

/// A CAVP test vector.
#[derive(Debug, Clone, Default)]
pub struct TestVector {
    out_len: usize,
    tests: Vec<Sha3Test>,
}

impl TestVector {
    /// Get the test slice
    pub fn tests(&self) -> &[Sha3Test] {
        &self.tests
    }

    /// Get the expected output length
    pub fn out_len(&self) -> usize {
        self.out_len
    }
}

/// Read a test vector file.
pub fn read_file(file: &str) -> Result<TestVector, Error> {
    let reader = BufReader::new(File::open(file).map_err(|_| Error::FileOpen)?);
    HashTv::read(reader)
}

/// Read a test vector from a string.
pub fn read_string(tv: &str) -> Result<TestVector, Error> {
    let reader = BufReader::new(tv.as_bytes());
    HashTv::read(reader)
}

#[cfg(test)]
mod tests {
    #[test]
    fn sha3() {
        let _ = pretty_env_logger::try_init();
        let tv = r"
# Sample test vector for SHA3 256

[L = 256]

Len = 0
Msg = 00
MD = a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a

Len = 8
Msg = e9
MD = f0d04dd1e6cfc29a4460d521796852f25d9ef8d28b44ee91ff5b759d72c1e6d6

Len = 16
Msg = d477
MD = 94279e8f5ccdf6e17f292b59698ab4e614dfe696a46c46da78305fc6a3146ab7
";
        let tv = super::read_string(tv).unwrap();
        eprintln!("tv: {tv:x?}");
    }
}
