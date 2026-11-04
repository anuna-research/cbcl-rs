//! Negative-test fixture generator only; this never produces a real proof.
use risc0_zkvm::{FakeReceipt, InnerReceipt, Receipt};
fn main() {
    let args: Vec<_> = std::env::args().collect();
    let receipt: Receipt = bincode::deserialize(&std::fs::read(&args[1]).unwrap()).unwrap();
    let fake = Receipt::new(
        InnerReceipt::Fake(FakeReceipt::new(receipt.inner.claim().unwrap())),
        receipt.journal.bytes,
    );
    std::fs::write(&args[2], bincode::serialize(&fake).unwrap()).unwrap();
}
