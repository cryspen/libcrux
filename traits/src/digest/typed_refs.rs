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

impl<'a, Algo: Hash> DigestMut<'a, Algo> {
    pub fn new_for_algo(algo: Algo, digest: &'a mut [u8]) -> Result<Self, WrongLengthError> {
        (digest.len() == algo.digest_len())
            .then_some(DigestMut {
                algorithm: algo,
                digest,
            })
            .ok_or(WrongLengthError)
    }
}

impl<Algo> AsMut<[u8]> for DigestMut<'_, Algo> {
    fn as_mut(&mut self) -> &mut [u8] {
        self.digest
    }
}

pub trait Hash: Copy + PartialEq {
    fn digest_len(&self) -> usize;

    fn hash<'a>(
        &self,
        digest: DigestMut<'a, Self>,
        payload: &[u8],
    ) -> Result<(), super::slice::HashError>;
}

impl<
        const DIGEST_LEN: usize,
        Algo: super::typed_owned::Hash<Digest = [u8; DIGEST_LEN]> + Copy + PartialEq,
    > Hash for Algo
{
    fn digest_len(&self) -> usize {
        DIGEST_LEN
    }
    fn hash<'a>(
        &self,
        mut digest: DigestMut<'a, Self>,
        payload: &[u8],
    ) -> Result<(), super::slice::HashError> {
        if self.digest_len() != digest.digest.len() {
            return Err(todo!());
        }

        let digest: &mut [u8; DIGEST_LEN] = digest
            .as_mut()
            .try_into()
            .map_err(|_| super::slice::HashError::Unknown)?;

        <Self as super::typed_owned::Hash>::hash(digest.into(), payload)
            .map_err(super::slice::HashError::from)
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
