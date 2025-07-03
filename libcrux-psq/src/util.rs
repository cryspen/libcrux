pub(crate) mod mlkem_pk_codec {
    pub(crate) fn tls_serialized_len(
        v: Option<&libcrux_ml_kem::mlkem768::MlKem768PublicKey>,
    ) -> usize {
        todo!()
    }

    pub(crate) fn tls_serialize(
        v: Option<&libcrux_ml_kem::mlkem768::MlKem768PublicKey>,
    ) -> Result<Vec<u8>, tls_codec::Error> {
        todo!()
    }
}

pub(crate) mod mlkem_ct_codec {
    use libcrux_ml_kem::mlkem768::MlKem768Ciphertext;
    use tls_codec::Error;

    pub(crate) fn tls_serialized_len(v: &MlKem768Ciphertext) -> usize {
        todo!()
    }

    pub(crate) fn tls_serialize(v: &MlKem768Ciphertext) -> Result<Vec<u8>, Error> {
        todo!()
    }

    pub(crate) fn tls_deserialize_bytes(
        bytes: &[u8],
    ) -> Result<(MlKem768Ciphertext, &[u8]), Error> {
        todo!()
    }
}
