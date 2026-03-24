//! Fuzz target: template expansion with arbitrary dialect + message pairs.
//!
//! Generates structured `PerformativeDef` values and argument lists, then
//! runs template expansion under resource bounds. Also exercises the evaluator
//! with arbitrary messages against a dialect registry. Must never panic.

#![no_main]

use arbitrary::Unstructured;
use cbcl_core::dialect::{Dialect, DialectRegistry, PerformativeDef, ResourceBounds};
use cbcl_core::evaluator::evaluate;
use cbcl_core::message::Message;
use cbcl_core::r2::ResourceState;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::template::{expand_template, expand_template_with_bindings, Bindings};
use libfuzzer_sys::fuzz_target;

fn arb_sexpr(u: &mut Unstructured, depth: u8) -> arbitrary::Result<SExpr> {
    if depth == 0 || u.ratio(1, 4)? {
        let variant: u8 = u.int_in_range(0..=4)?;
        match variant {
            0 => Ok(SExpr::Atom(Atom::Symbol(arb_short_string(u)?))),
            1 => Ok(SExpr::Atom(Atom::Str(arb_short_string(u)?))),
            2 => Ok(SExpr::Atom(Atom::Num(u.arbitrary()?))),
            3 => Ok(SExpr::Atom(Atom::Bool(u.arbitrary()?))),
            _ => Ok(SExpr::Atom(Atom::Keyword(arb_short_string(u)?))),
        }
    } else {
        let len: u8 = u.int_in_range(0..=6)?;
        let items: arbitrary::Result<Vec<SExpr>> =
            (0..len).map(|_| arb_sexpr(u, depth - 1)).collect();
        Ok(SExpr::List(items?))
    }
}

fn arb_short_string(u: &mut Unstructured) -> arbitrary::Result<String> {
    let len: usize = u.int_in_range(0..=16)?;
    let bytes: Vec<u8> = (0..len)
        .map(|_| u.int_in_range(b'a'..=b'z'))
        .collect::<arbitrary::Result<_>>()?;
    Ok(String::from_utf8(bytes).unwrap())
}

fn arb_performative(u: &mut Unstructured) -> arbitrary::Result<PerformativeDef> {
    let name = arb_short_string(u)?;
    let param_count: u8 = u.int_in_range(0..=4)?;
    let params: arbitrary::Result<Vec<SExpr>> = (0..param_count)
        .map(|_| Ok(SExpr::Atom(Atom::Symbol(arb_short_string(u)?))))
        .collect();
    let template = arb_sexpr(u, 4)?;
    Ok(PerformativeDef {
        name,
        params: params?,
        template,
    })
}

fn arb_dialect(u: &mut Unstructured) -> arbitrary::Result<Dialect> {
    let name = arb_short_string(u)?;
    let perf_count: u8 = u.int_in_range(1..=5)?;
    let performatives: arbitrary::Result<Vec<PerformativeDef>> =
        (0..perf_count).map(|_| arb_performative(u)).collect();
    let max_depth: u32 = u.int_in_range(2..=16)?;
    let max_expansion_size: u32 = u.int_in_range(64..=2048)?;
    Ok(Dialect {
        name,
        extends: vec!["cbcl".into()],
        author: None,
        performatives: performatives?,
        resources: ResourceBounds {
            max_depth,
            max_expansion_size,
            verification_time_ms: 10,
        },
        examples: vec![],
        signature: None,
        hash: None,
        protocol: None,
    })
}

fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(data);

    // Generate dialect and pick a performative to expand.
    let dialect = match arb_dialect(&mut u) {
        Ok(d) => d,
        Err(_) => return,
    };

    if dialect.performatives.is_empty() {
        return;
    }

    let perf_idx: usize = match u.int_in_range(0..=(dialect.performatives.len() - 1)) {
        Ok(i) => i,
        Err(_) => return,
    };
    let def = &dialect.performatives[perf_idx];

    // Generate arguments matching param count.
    let args: Vec<SExpr> = match (0..def.params.len())
        .map(|_| arb_sexpr(&mut u, 3))
        .collect::<arbitrary::Result<Vec<_>>>()
    {
        Ok(a) => a,
        Err(_) => return,
    };

    // expand_template must not panic.
    let mut rs = ResourceState::new(
        dialect.resources.max_depth,
        dialect.resources.max_expansion_size,
    );
    let _ = expand_template(def, &args, &mut rs);

    // expand_template_with_bindings with arbitrary bindings.
    let binding_count: u8 = u.int_in_range(0..=4).unwrap_or(0);
    let mut bindings = Bindings::new();
    for _ in 0..binding_count {
        if let (Ok(k), Ok(v)) = (arb_short_string(&mut u), arb_sexpr(&mut u, 2)) {
            bindings.insert(k, v);
        }
    }
    let template = match arb_sexpr(&mut u, 4) {
        Ok(t) => t,
        Err(_) => return,
    };
    let mut rs2 = ResourceState::new(
        dialect.resources.max_depth,
        dialect.resources.max_expansion_size,
    );
    let _ = expand_template_with_bindings(&template, &bindings, &mut rs2);

    // Exercise the evaluator: install dialect and evaluate a message.
    let mut registry = DialectRegistry::new();
    if registry.install(dialect.clone()).is_ok() {
        // Try to parse/construct a message that uses this dialect.
        if let Some(perf_name) = dialect.performatives.first().map(|p| &p.name) {
            use cbcl_core::message::Performative;
            let msg = Message::Simple {
                performative: Performative::Custom(perf_name.clone()),
                recipient: None,
                content: args.first().cloned().unwrap_or(SExpr::List(vec![])),
                params: args.clone(),
                thread: None,
                sender: None,
                caused_by: None,
            };
            let _ = evaluate(&msg, &registry);
        }
    }
});
