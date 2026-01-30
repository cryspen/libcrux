/// CSHAKE128 Iterative state
pub struct CShake128It {
    state: KeccakXofState<1, 168, u64>,
}
