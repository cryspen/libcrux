pub struct DigestMut<'a, Algo> {
    algorithm: Algo,
    digest: &'a mut [u8],
}

impl<Algo> DigestMut<'_, Algo> {
    pub fn algo(&self) -> &Algo {
        &self.algorithm
    }
}

#[derive(Debug, Clone, Copy)]
pub struct WrongLengthError;

#[derive(Debug, Clone, Copy)]
pub enum HashError {
    InvalidDigestLength,
    WrongDigest,
    InvalidPayloadLength,
    Unknown,
}

impl From<super::slice::HashError> for HashError {
    fn from(e: super::slice::HashError) -> Self {
        match e {
            super::slice::HashError::InvalidDigestLength => HashError::InvalidDigestLength,
            super::slice::HashError::InvalidPayloadLength => HashError::InvalidPayloadLength,
            super::slice::HashError::Unknown => HashError::Unknown,
        }
    }
}
impl From<super::arrayref::HashError> for HashError {
    fn from(e: super::arrayref::HashError) -> Self {
        match e {
            super::arrayref::HashError::InvalidDigestLength => HashError::InvalidDigestLength,
            super::arrayref::HashError::InvalidPayloadLength => HashError::InvalidPayloadLength,
            super::arrayref::HashError::Unknown => HashError::Unknown,
        }
    }
}

impl<'a, Algo: Hash> DigestMut<'a, Algo> {
    pub fn new_for_algo(algo: Algo, digest: &'a mut [u8]) -> Result<Self, WrongLengthError> {
        // check that digest length matches, if available
        if !algo.digest_len_is_valid(digest.len()) {
            return Err(WrongLengthError);
        }

        Ok(DigestMut {
            algorithm: algo,
            digest,
        })
    }
}

impl<Algo> AsMut<[u8]> for DigestMut<'_, Algo> {
    fn as_mut(&mut self) -> &mut [u8] {
        self.digest
    }
}

pub trait Hash: Copy + PartialEq {
    fn digest_len_is_valid(&self, len: usize) -> bool;

    fn hash<'a>(&self, digest: DigestMut<'a, Self>, payload: &[u8]) -> Result<(), HashError>;

    fn new_digest<'a>(self, digest: &'a mut [u8]) -> Result<DigestMut<'a, Self>, WrongLengthError> {
        DigestMut::new_for_algo(self, digest)
    }
}

impl<
        const DIGEST_LEN: usize,
        Algo: super::typed_owned::Hash<Digest = [u8; DIGEST_LEN]> + Copy + PartialEq,
    > Hash for Algo
{
    fn digest_len_is_valid(&self, digest_len: usize) -> bool {
        digest_len == DIGEST_LEN
    }
    fn hash<'a>(&self, mut digest: DigestMut<'a, Self>, payload: &[u8]) -> Result<(), HashError> {
        if DIGEST_LEN != digest.digest.len() {
            return Err(HashError::InvalidDigestLength);
        }

        let digest: &mut [u8; DIGEST_LEN] =
            digest.as_mut().try_into().map_err(|_| HashError::Unknown)?;

        <Self as super::typed_owned::Hash>::hash(digest.into(), payload).map_err(HashError::from)
    }
}

pub trait MultiplexesHash<Algo>: Hash + Sized {
    fn mux_algo(&self) -> Option<Algo>;

    fn wrap_algo(algo: Algo) -> Self;

    fn mux_digest<'a>(digest: DigestMut<'a, Self>) -> Option<DigestMut<'a, Algo>> {
        let DigestMut { algorithm, digest } = digest;
        algorithm
            .mux_algo()
            .map(|algorithm| DigestMut { algorithm, digest })
    }
}
