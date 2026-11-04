#![no_main]
risc0_zkvm::guest::entry!(main);
fn main() {
    let length: u32 = risc0_zkvm::guest::env::read();
    assert!(length as usize <= checkpoint_common::MAX_INPUT);
    let mut bytes = vec![0u8; length as usize];
    risc0_zkvm::guest::env::read_slice(&mut bytes);
    let result = checkpoint_common::compute(&bytes).expect("invalid checkpoint input");
    risc0_zkvm::guest::env::commit(&result.journal);
}
