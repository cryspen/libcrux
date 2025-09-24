pub trait Prf<OutMut, Key, Message> {
    type Error;

    fn eval(out: OutMut, k: Key, msg: Message) -> Result<(), Self::Error>;
}

mod hmac;
