//! Fuzz target: role-layer recognisers with arbitrary bytes (SPEC-014
//! TEST-638).
//!
//! Parses raw bytes as an S-expression, then drives `parse_roles`,
//! `parse_cast`, the recipient-set message extension, and the with-roles
//! wrapper parse. Must never panic; malformed input must be rejected, never
//! repaired (CON-600/601, LangSec principle 4).

#![no_main]

use cbcl_core::message::Message;
use cbcl_core::role::{parse_cast, parse_roles};
use cbcl_parser::parse;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let Ok(text) = core::str::from_utf8(data) else {
        return;
    };
    let Ok(sexpr) = parse(text) else {
        return;
    };
    // Role declarations: must return Ok or a typed violation, never panic.
    let roles = parse_roles(&sexpr).unwrap_or_default();
    // Cast bindings against whatever roles parsed (possibly none).
    let _ = parse_cast(&sexpr, &roles);
    // Message layer: recipient sets and the with-roles wrapper.
    if let Ok(msg) = Message::try_from(&sexpr) {
        // Round-trip oracle (TEST-638): serialising a parsed message must
        // yield output that re-parses to an *equal* message, i.e.
        // parse ∘ serialise = identity. This catches serializer/parser
        // divergence (a lost field, a canonicalisation mismatch, a form the
        // serializer emits but the parser rejects) — not merely a crash.
        let back = cbcl_core::sexpr::SExpr::from(&msg);
        let reparsed = Message::try_from(&back)
            .expect("serialising a parsed message must yield re-parseable output");
        assert_eq!(
            msg, reparsed,
            "message round-trip must be the identity: parse(serialise(m)) == m"
        );
        let _ = msg.recipient_set();
    }
});
