//! Shared proptest generators for CBCL types.

use cbcl_core::dialect::{Dialect, PerformativeDef, ResourceBounds};
use cbcl_core::message::{CorePerformative, Message, Performative, CORE_PERFORMATIVE_NAMES};
use cbcl_core::sexpr::{Atom, SExpr};
use proptest::prelude::*;

// ---------------------------------------------------------------------------
// Atom generators
// ---------------------------------------------------------------------------

pub fn arb_symbol_name() -> impl Strategy<Value = String> {
    // Symbol chars: alphanumeric, _, -, ., /, !, ?, +, *, <, >, =, @
    // Must not be empty, must not parse as a number or bool literal
    prop::string::string_regex("[a-zA-Z][a-zA-Z0-9_\\-]*")
        .unwrap()
        .prop_filter("must not be empty", |s| !s.is_empty())
        .prop_filter("must not be a core keyword", |s| {
            s != "meta" && s != "lang" && s != "envelope" && s != "signed" && s != "with-limits"
        })
}

pub fn arb_custom_perf_name() -> impl Strategy<Value = String> {
    arb_symbol_name().prop_filter("must not be core performative", |s| {
        !CORE_PERFORMATIVE_NAMES.contains(&s.as_str())
    })
}

pub fn arb_keyword_name() -> impl Strategy<Value = String> {
    prop::string::string_regex("[a-zA-Z][a-zA-Z0-9_\\-]*")
        .unwrap()
        .prop_filter("must not be empty", |s| !s.is_empty())
        .prop_filter("must not be thread or sender", |s| {
            s != "thread" && s != "sender"
        })
}

pub fn arb_safe_string() -> impl Strategy<Value = String> {
    // Strings that round-trip cleanly through serialization
    prop::string::string_regex("[a-zA-Z0-9 _\\-\\.!?,;:]+")
        .unwrap()
        .prop_filter("must not be empty", |s| !s.is_empty())
}

pub fn arb_atom() -> impl Strategy<Value = Atom> {
    prop_oneof![
        arb_symbol_name().prop_map(Atom::Symbol),
        arb_safe_string().prop_map(Atom::Str),
        any::<i64>().prop_map(Atom::Num),
        any::<bool>().prop_map(Atom::Bool),
        arb_keyword_name().prop_map(Atom::Keyword),
    ]
}

// ---------------------------------------------------------------------------
// SExpr generators (bounded depth)
// ---------------------------------------------------------------------------

pub fn arb_sexpr(max_depth: u32) -> impl Strategy<Value = SExpr> {
    arb_atom().prop_map(SExpr::Atom).prop_recursive(
        max_depth, // max depth
        64,        // max nodes
        4,         // items per collection
        |inner| prop::collection::vec(inner, 0..5).prop_map(SExpr::List),
    )
}

// ---------------------------------------------------------------------------
// ResourceBounds generators
// ---------------------------------------------------------------------------

pub fn arb_valid_resource_bounds() -> impl Strategy<Value = ResourceBounds> {
    (1u32..=64, 1u32..=8192, 1u32..=1000).prop_map(|(d, e, v)| ResourceBounds {
        max_depth: d,
        max_expansion_size: e,
        verification_time_ms: v,
    })
}

pub fn arb_invalid_resource_bounds() -> impl Strategy<Value = ResourceBounds> {
    prop_oneof![
        // zero depth
        (Just(0u32), 1u32..=8192, 1u32..=1000).prop_map(|(d, e, v)| ResourceBounds {
            max_depth: d,
            max_expansion_size: e,
            verification_time_ms: v,
        }),
        // zero expansion
        (1u32..=64, Just(0u32), 1u32..=1000).prop_map(|(d, e, v)| ResourceBounds {
            max_depth: d,
            max_expansion_size: e,
            verification_time_ms: v,
        }),
        // zero verification time
        (1u32..=64, 1u32..=8192, Just(0u32)).prop_map(|(d, e, v)| ResourceBounds {
            max_depth: d,
            max_expansion_size: e,
            verification_time_ms: v,
        }),
        // depth too large
        (65u32..=200, 1u32..=8192, 1u32..=1000).prop_map(|(d, e, v)| ResourceBounds {
            max_depth: d,
            max_expansion_size: e,
            verification_time_ms: v,
        }),
        // expansion too large
        (1u32..=64, 8193u32..=20000, 1u32..=1000).prop_map(|(d, e, v)| ResourceBounds {
            max_depth: d,
            max_expansion_size: e,
            verification_time_ms: v,
        }),
        // verification time too large
        (1u32..=64, 1u32..=8192, 1001u32..=5000).prop_map(|(d, e, v)| ResourceBounds {
            max_depth: d,
            max_expansion_size: e,
            verification_time_ms: v,
        }),
    ]
}

// ---------------------------------------------------------------------------
// PerformativeDef generators
// ---------------------------------------------------------------------------

/// A performative def that does NOT self-reference (passes R1).
pub fn arb_safe_performative_def() -> impl Strategy<Value = PerformativeDef> {
    (arb_custom_perf_name(), arb_sexpr(2)).prop_map(|(name, template)| {
        // Ensure template doesn't contain the performative name as a symbol
        let safe_template = sanitize_template(&name, &template);
        PerformativeDef {
            role: None,
            name,
            params: Vec::new(),
            template: safe_template,
        }
    })
}

/// Replace any occurrence of `name` as a symbol in the expression with "safe-placeholder".
fn sanitize_template(name: &str, expr: &SExpr) -> SExpr {
    match expr {
        SExpr::Atom(Atom::Symbol(s)) if s == name => {
            SExpr::Atom(Atom::Symbol(String::from("safe-placeholder")))
        }
        SExpr::Atom(_) => expr.clone(),
        SExpr::List(items) => {
            SExpr::List(items.iter().map(|e| sanitize_template(name, e)).collect())
        }
    }
}

/// A performative def that DOES self-reference (fails R1).
pub fn arb_recursive_performative_def() -> impl Strategy<Value = PerformativeDef> {
    arb_custom_perf_name().prop_map(|name| {
        let template = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol(String::from("literal"))),
            SExpr::List(vec![
                SExpr::Atom(Atom::Symbol(name.clone())),
                SExpr::Atom(Atom::Symbol(String::from("x"))),
            ]),
        ]);
        PerformativeDef {
            role: None,
            name,
            params: Vec::new(),
            template,
        }
    })
}

// ---------------------------------------------------------------------------
// Dialect generators
// ---------------------------------------------------------------------------

/// A valid dialect that passes R1, R2, R3.
pub fn arb_valid_dialect() -> impl Strategy<Value = Dialect> {
    (
        arb_custom_perf_name(),
        arb_valid_resource_bounds(),
        prop::collection::vec(arb_safe_performative_def(), 0..3),
    )
        .prop_map(|(name, resources, performatives)| {
            let perf_names = performatives
                .iter()
                .map(|perf| perf.name.clone())
                .collect::<Vec<_>>();
            let performatives = performatives
                .into_iter()
                .map(|mut perf| {
                    for perf_name in &perf_names {
                        perf.template = sanitize_template(perf_name, &perf.template);
                    }
                    perf
                })
                .collect();

            Dialect {
                roles: Vec::new(),
                causal_locality: Default::default(),
                name,
                extends: vec![String::from("cbcl")],
                author: None,
                performatives,
                resources,
                examples: Vec::new(),
                signature: None,
                hash: None,
                protocol: None,
                causal_protocol: None,
                shapes: Vec::new(),
            }
        })
}

/// A dialect with an R3 violation (redefines a core performative).
pub fn arb_r3_violating_dialect() -> impl Strategy<Value = Dialect> {
    (
        arb_custom_perf_name(),
        arb_valid_resource_bounds(),
        prop::sample::select(CORE_PERFORMATIVE_NAMES),
    )
        .prop_map(|(dialect_name, resources, core_name)| Dialect {
            roles: Vec::new(),
            causal_locality: Default::default(),
            name: dialect_name,
            extends: vec![String::from("cbcl")],
            author: None,
            performatives: vec![PerformativeDef {
                role: None,
                name: String::from(core_name),
                params: Vec::new(),
                template: SExpr::List(vec![
                    SExpr::Atom(Atom::Symbol(String::from("effect"))),
                    SExpr::Atom(Atom::Symbol(String::from("custom"))),
                ]),
            }],
            resources,
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None,
            causal_protocol: None,
            shapes: Vec::new(),
        })
}

// ---------------------------------------------------------------------------
// Message generators
// ---------------------------------------------------------------------------

pub fn arb_core_performative() -> impl Strategy<Value = CorePerformative> {
    prop_oneof![
        Just(CorePerformative::Tell),
        Just(CorePerformative::Ask),
        Just(CorePerformative::Reply),
        Just(CorePerformative::Error),
        Just(CorePerformative::Ok),
        Just(CorePerformative::Cancel),
        Just(CorePerformative::Hello),
        Just(CorePerformative::Bye),
    ]
}

pub fn arb_performative() -> impl Strategy<Value = Performative> {
    prop_oneof![
        arb_core_performative().prop_map(Performative::Core),
        arb_custom_perf_name().prop_map(Performative::Custom),
    ]
}

/// Atom that is not a keyword (safe for message content position).
fn arb_non_keyword_atom() -> impl Strategy<Value = Atom> {
    prop_oneof![
        arb_symbol_name()
            .prop_filter("not @-prefixed", |s| !s.starts_with('@'))
            .prop_map(Atom::Symbol),
        arb_safe_string().prop_map(Atom::Str),
        any::<i64>().prop_map(Atom::Num),
        any::<bool>().prop_map(Atom::Bool),
    ]
}

/// SExpr safe for message content: no top-level keywords, no @-prefixed symbols at top.
fn arb_message_content() -> impl Strategy<Value = SExpr> {
    arb_non_keyword_atom()
        .prop_map(SExpr::Atom)
        .prop_recursive(2, 32, 4, |inner| {
            prop::collection::vec(inner, 0..4).prop_map(SExpr::List)
        })
}

pub fn arb_simple_message() -> impl Strategy<Value = Message> {
    (
        arb_performative(),
        prop::option::of(arb_symbol_name().prop_map(|s| format!("@{}", s))),
        arb_message_content(),
        prop::option::of(arb_symbol_name()),
        prop::option::of(arb_symbol_name().prop_map(|s| format!("@{}", s))),
    )
        .prop_map(
            |(performative, recipient, content, thread, sender)| Message::Simple {
                performative,
                recipient: recipient.map(cbcl_core::message::Recipients::One),
                content,
                params: Vec::new(),
                thread,
                sender,
                caused_by: None,
            },
        )
}

use std::string::String;
use std::vec::Vec;
