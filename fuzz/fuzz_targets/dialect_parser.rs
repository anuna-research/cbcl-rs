//! Fuzz target: dialect parser with arbitrary bytes.
//!
//! Parses raw bytes as an S-expression, then attempts to interpret it as a
//! dialect definition via `parse_dialect` and `parse_meta_define`. Must never
//! panic.

#![no_main]

use cbcl_parser::{parse, parse_dialect, parse_meta_define};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let input = match std::str::from_utf8(data) {
        Ok(s) => s,
        Err(_) => return,
    };

    if let Ok(sexpr) = parse(input) {
        let _ = parse_dialect(&sexpr);
        let _ = parse_meta_define(&sexpr);
    }
});
