//! Fuzz target: S-expression parser with arbitrary bytes.
//!
//! Feeds raw byte slices (interpreted as UTF-8 where possible) into
//! `cbcl_parser::parse` and `parse_with_fuel`. The parser must never
//! panic — it should return `Ok` or `Err` for every input.
//!
//! Additionally tests the round-trip property: parse(serialize(parse(input))) == parse(input).

#![no_main]

use cbcl_core::serializer::serialize;
use cbcl_parser::parse;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let input = match std::str::from_utf8(data) {
        Ok(s) => s,
        Err(_) => return,
    };

    // Parser must not panic on any input.
    if let Ok(expr) = parse(input) {
        // Round-trip: serialize then re-parse must produce the same tree.
        let serialized = serialize(&expr);
        let reparsed =
            parse(&serialized).expect("round-trip: serialized output must parse successfully");
        assert_eq!(expr, reparsed, "round-trip mismatch");
    }
});
