//! Fuzz target: message parser with arbitrary bytes.
//!
//! Parses raw bytes as an S-expression, then attempts to interpret it as a
//! CBCL message. Also exercises the full `run_pipeline` path. Neither path
//! should ever panic.

#![no_main]

use cbcl_parser::{parse, parse_message, run_pipeline};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let input = match std::str::from_utf8(data) {
        Ok(s) => s,
        Err(_) => return,
    };

    // Two-stage: parse sexpr, then interpret as message.
    if let Ok(sexpr) = parse(input) {
        let _ = parse_message(&sexpr);
    }

    // Full pipeline: parse → validate → result. Must not panic.
    let _ = run_pipeline(input);
});
