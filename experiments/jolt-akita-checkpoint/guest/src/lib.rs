#![cfg_attr(feature = "guest", no_std)]
extern crate alloc;
use alloc::vec::Vec;
#[jolt::provable(
    heap_size = 67108864,
    stack_size = 1048576,
    max_input_size = 0,
    max_trusted_advice_size = 0,
    max_untrusted_advice_size = 2097152,
    max_output_size = 8192,
    max_trace_length = 1073741824
)]
fn checkpoint(input: jolt::UntrustedAdvice<Vec<u8>>) -> Vec<u8> {
    let computed = checkpoint_common::compute(&input).expect("invalid checkpoint input");
    serde_json::to_vec(&computed.journal).expect("journal encoding")
}
