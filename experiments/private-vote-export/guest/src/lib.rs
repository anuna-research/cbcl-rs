#![cfg_attr(feature = "guest", no_std)]
extern crate alloc;
use alloc::vec::Vec;
#[jolt::provable(
    heap_size = 16777216,
    stack_size = 1048576,
    max_input_size = 0,
    max_trusted_advice_size = 0,
    max_untrusted_advice_size = 131072,
    max_output_size = 8192,
    max_trace_length = 16777216
)]
fn export_vote(input: jolt::UntrustedAdvice<Vec<u8>>) -> Vec<u8> {
    serde_json::to_vec(&vote_common::compute(&input)).expect("result serialization")
}
