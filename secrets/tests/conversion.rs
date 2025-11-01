use libcrux_secrets::{
    Classify, Declassify, SecretByteArray, SecretByteArrayRef, SecretByteArrayRefMut,
    SecretByteSlice, SecretByteSliceMut, U8,
};

fn mut_byte_slice_fun<'a>(x: impl SecretByteSliceMut<'a>) {
    let x = x.classify();
    x[0] = 5.classify();
}

fn byte_slice_fun<'a>(x: impl SecretByteSlice<'a>) -> U8 {
    let x = x.classify();
    x[0]
}

fn mut_byte_array_ref_fun<'a>(x: impl SecretByteArrayRefMut<'a, 4>) {
    let x = x.classify();
    x[0] = 5.classify();
}

fn byte_array_ref_fun<'a>(x: impl SecretByteArrayRef<'a, 4>) -> U8 {
    let x = x.classify();
    x[0]
}

fn byte_array_fun<'a>(x: impl SecretByteArray<4>) -> U8 {
    let x = x.classify();
    x[0]
}

#[test]
fn to_secret_mut() {
    let mut x = [0u8; 4];

    mut_byte_slice_fun(x.as_mut_slice());
    assert_eq!(x[0], 5);

    mut_byte_array_ref_fun(&mut x);
    assert_eq!(x[0], 5);
}

#[test]
fn to_secret() {
    let x = [0x13u8; 4];

    let result = byte_slice_fun(x.as_slice());
    assert_eq!(result.declassify(), 0x13);

    let result = byte_array_ref_fun(&x);
    assert_eq!(result.declassify(), 0x13);

    let result = byte_array_fun(x);
    assert_eq!(result.declassify(), 0x13);
}
