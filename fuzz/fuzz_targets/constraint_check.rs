//! Fuzz target: constraint verification (R1–R3) with arbitrary SExpr trees.
//!
//! Generates structured `Dialect` values with arbitrary performative
//! definitions, then runs all constraint checks. None should panic.

#![no_main]

use arbitrary::Unstructured;
use cbcl_core::dialect::{Dialect, DialectRegistry, PerformativeDef, ResourceBounds};
use cbcl_core::r1::{r1_violations, verify_r1, verify_r1_dialect};
use cbcl_core::r2::{bounded_eval, verify_r2, ResourceState};
use cbcl_core::r3::{r3_violations, verify_r3};
use cbcl_core::sexpr::{Atom, SExpr};
use libfuzzer_sys::fuzz_target;

/// Arbitrary SExpr generation with bounded depth.
fn arb_sexpr(u: &mut Unstructured, depth: u8) -> arbitrary::Result<SExpr> {
    if depth == 0 || u.ratio(1, 4)? {
        // Generate atom
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
    let perf_count: u8 = u.int_in_range(0..=5)?;
    let performatives: arbitrary::Result<Vec<PerformativeDef>> =
        (0..perf_count).map(|_| arb_performative(u)).collect();
    let max_depth: u32 = u.int_in_range(1..=64)?;
    let max_expansion_size: u32 = u.int_in_range(1..=8192)?;
    let verification_time_ms: u32 = u.int_in_range(1..=1000)?;
    Ok(Dialect {
        name,
        extends: vec!["cbcl".into()],
        author: None,
        performatives: performatives?,
        resources: ResourceBounds {
            max_depth,
            max_expansion_size,
            verification_time_ms,
        },
        examples: vec![],
        signature: None,
        hash: None,
        protocol: None,
    })
}

fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(data);

    // Generate an arbitrary dialect.
    let dialect = match arb_dialect(&mut u) {
        Ok(d) => d,
        Err(_) => return,
    };

    // R1: no-recursion check must not panic.
    let _ = verify_r1_dialect(&dialect);
    let _ = r1_violations(&dialect);
    for p in &dialect.performatives {
        let _ = verify_r1(&p.name, &p.template);
    }

    // R2: resource bounds check must not panic.
    let _ = verify_r2(&dialect);

    // R3: core preservation check must not panic.
    let _ = verify_r3(&dialect);
    let _ = r3_violations(&dialect);

    // bounded_eval with an arbitrary expression.
    if let Ok(expr) = arb_sexpr(&mut u, 4) {
        let mut rs = ResourceState::new(
            dialect.resources.max_depth.min(32),
            dialect.resources.max_expansion_size.min(4096),
        );
        let _ = bounded_eval(100, &expr, &mut rs);
    }

    // Attempt dialect installation into registry.
    let mut registry = DialectRegistry::new();
    let _ = registry.install(dialect);
});
