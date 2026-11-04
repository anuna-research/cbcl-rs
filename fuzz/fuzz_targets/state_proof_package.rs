//! Fuzz target: SPEC-035 package recognisers with arbitrary bytes (TEST-3507
//! depth run). `Proof::from_json` and `Chain::from_json` must return `Ok` or
//! `Err` and never panic; the result is otherwise ignored.

#![no_main]

use cbcl_state_proof::{Chain, Proof};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let _ = Proof::from_json(data);
    let _ = Chain::from_json(data);
});
