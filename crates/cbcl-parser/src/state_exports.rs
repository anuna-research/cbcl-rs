//! SPEC-019 R.7: the state-layer exports, as one implementation every
//! binding wraps (SPEC-010 REQ-002: a binding adds term translation and
//! crash containment, never semantics).
//!
//! Frames are S-expressions, like every other export; state, schema, and
//! rejections come back as canonical JSON (SPEC-019 R.3), a canonical act as
//! its wire text, and a self-address as `sha256-<hex>`.
//!
//! ```text
//! (fold               <dialect> <thread> (acts (<signer> <message>) …))        → state JSON
//! (intend             <dialect> <thread> (acts …) <signer> <verb> (:k v …))    → canonical act
//! (verify-state-shape <dialect> <message>)                                     → "ok"
//! (state-schema       <dialect>)                                               → schema JSON
//! (may-send           <dialect> <thread> (acts …) <signer>)                    → JSON array of verbs
//! (frontier           <dialect> <thread> (acts …))                             → {"instance","frontier"}
//! (admit              <dialect> <thread> (acts …) (<signer> <message>))        → {"verdict":…}
//! (define …)                                                                   → sha256-<hex>   (dialect_hash)
//! ```
//!
//! `<dialect>` is a `(define …)` or a `(dialects <ancestor>* <leaf>)` chain,
//! installed through the full R1–R7 pipeline by [`parse_and_install_dialect`];
//! the leaf is the dialect judged. Each act entry is the complete received
//! message with the signer the host authenticated; the cast is read from the
//! root among the acts and never supplied.

#![forbid(unsafe_code)]

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use cbcl_core::blame::ViolationError;
use cbcl_core::canonical::{dialect_hash, dialect_name};
use cbcl_core::dialect::{Dialect, DialectRegistry};
use cbcl_core::intend::{canonical_text, cast_of, intend, may_send, render_reject, Instance};
use cbcl_core::projection::verify_causal_for_role;
use cbcl_core::protocol::{verify_causal, VerificationResult};
use cbcl_core::role::{AgentKey, Endpoint};
use cbcl_core::serializer::serialize;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::state::{fold, frontier, render_json, render_schema, state_schema, Act, Value};
use cbcl_core::store::{ContentHash, MessageStore, ThreadId};

/// Parse a dialect S-expression, or a `(dialects <ancestor>* <leaf>)` chain,
/// and install each into a fresh registry through the full R1–R7 pipeline,
/// checking a declared `:hash` against the canonical hash of the installed
/// dialect. Ancestors precede the leaf so R5 resolves parent performatives.
///
/// Shared by every binding's dialect-taking export so no caller can bypass
/// install-time well-formedness.
pub fn parse_and_install_dialect(dialect_sexpr: &SExpr) -> Result<DialectRegistry, String> {
    let forms: Vec<&SExpr> = match dialect_sexpr {
        SExpr::List(xs) if matches!(xs.first(), Some(SExpr::Atom(Atom::Symbol(s))) if s == "dialects") =>
        {
            if xs.len() < 2 {
                return Err(String::from(
                    "(dialects ...) must contain at least one (define ...) form",
                ));
            }
            xs[1..].iter().collect()
        }
        _ => alloc::vec![dialect_sexpr],
    };
    let mut registry = DialectRegistry::new();
    for form in &forms {
        let dialect =
            crate::parse_dialect(form).map_err(|e| format!("dialect parse error: {e}"))?;
        registry
            .install(dialect)
            .map_err(|e| format!("dialect verification failed: {e}"))?;
        // A declared `:hash` must be the canonical hash of what was installed;
        // blame attribution surfaces it, so an unchecked claim could mislabel
        // which dialect signed a verdict. Checked on every link of a chain.
        let installed = registry
            .get(registry.len() - 1)
            .ok_or_else(|| String::from("internal: just-installed dialect not found"))?;
        if let Some(claimed) = &installed.hash {
            let computed = dialect_hash(installed);
            if claimed != &computed {
                return Err(format!(
                    "dialect verification failed: declared :hash {claimed} does not match canonical hash {computed}"
                ));
            }
        }
    }
    Ok(registry)
}

fn leaf(registry: &DialectRegistry) -> Result<Dialect, String> {
    registry
        .iter()
        .last()
        .cloned()
        .ok_or_else(|| String::from("no dialect installed"))
}

fn atom_text(s: &SExpr, what: &str) -> Result<String, String> {
    match s {
        SExpr::Atom(Atom::Str(x)) | SExpr::Atom(Atom::Symbol(x)) => Ok(x.clone()),
        other => Err(format!("{what} must be a string or symbol, got {other}")),
    }
}

fn parse_frame(input: &str, head: &str) -> Result<Vec<SExpr>, String> {
    let sexpr = crate::parser::parse(input).map_err(|e| format!("parse error: {e}"))?;
    match sexpr {
        SExpr::List(items) if matches!(items.first(), Some(SExpr::Atom(Atom::Symbol(s))) if s == head) => {
            Ok(items[1..].to_vec())
        }
        _ => Err(format!("expected ({head} …)")),
    }
}

fn parse_acts(sexpr: &SExpr) -> Result<Vec<Act>, String> {
    let items = match sexpr {
        SExpr::List(items) if matches!(items.first(), Some(SExpr::Atom(Atom::Symbol(s))) if s == "acts") => {
            &items[1..]
        }
        _ => return Err(String::from("expected (acts (<signer> <message>) …)")),
    };
    let mut acts = Vec::new();
    for entry in items {
        let SExpr::List(pair) = entry else {
            return Err(String::from("an act entry is (<signer> <message>)"));
        };
        if pair.len() != 2 {
            return Err(String::from("an act entry is (<signer> <message>)"));
        }
        let signer = atom_text(&pair[0], "signer")?;
        let message =
            crate::parse_message(&pair[1]).map_err(|e| format!("message parse error: {e}"))?;
        acts.push(Act::from_message(message, &signer)?);
    }
    Ok(acts)
}

type InstanceFrame = (Dialect, ThreadId, Vec<Act>, Vec<SExpr>);

fn instance_frame(input: &str, head: &str) -> Result<InstanceFrame, String> {
    let items = parse_frame(input, head)?;
    if items.len() < 3 {
        return Err(format!("expected ({head} <dialect> <thread> (acts …) …)"));
    }
    let registry = parse_and_install_dialect(&items[0])?;
    let dialect = leaf(&registry)?;
    let thread = ThreadId(atom_text(&items[1], "thread")?);
    let acts = parse_acts(&items[2])?;
    Ok((dialect, thread, acts, items[3..].to_vec()))
}

/// `(fold <dialect> <thread> (acts …))` → the state as canonical JSON.
pub fn fold_str(input: &str) -> Result<String, String> {
    let (d, _thread, acts, _) = instance_frame(input, "fold")?;
    let clause = d
        .state
        .as_ref()
        .ok_or_else(|| String::from("dialect has no state clause"))?;
    Ok(render_json(&fold(
        clause,
        d.causal_protocol.as_ref(),
        &acts,
    )))
}

/// `(intend <dialect> <thread> (acts …) <signer> <verb> (:k v …))` → the
/// canonical act for the host to sign, or `Err` with a JSON rejection.
pub fn intend_str(input: &str) -> Result<String, String> {
    let (d, thread, acts, rest) = instance_frame(input, "intend")?;
    if rest.len() != 3 {
        return Err(String::from(
            "expected (intend <dialect> <thread> (acts …) <signer> <verb> (:k v …))",
        ));
    }
    let signer = AgentKey(atom_text(&rest[0], "signer")?);
    let verb = atom_text(&rest[1], "verb")?;
    let SExpr::List(kv) = &rest[2] else {
        return Err(String::from(
            "fields must be a list of :keyword value pairs",
        ));
    };
    let mut fields = BTreeMap::new();
    let mut i = 0;
    while i + 1 < kv.len() {
        if let SExpr::Atom(Atom::Keyword(k)) = &kv[i] {
            fields.insert(k.clone(), kv[i + 1].clone());
        }
        i += 2;
    }
    let inst = Instance::new(&d, thread, &acts)?;
    match intend(&inst, &signer, &verb, fields) {
        Ok(m) => Ok(canonical_text(&m)),
        Err(r) => Err(render_reject(&r)),
    }
}

/// `(verify-state-shape <dialect> <message>)` → `"ok"`, or `Err` with a
/// REQ-233 blame S-expression.
pub fn verify_state_shape_str(input: &str) -> Result<String, String> {
    let items = parse_frame(input, "verify-state-shape")?;
    if items.len() != 2 {
        return Err(String::from(
            "expected (verify-state-shape <dialect> <message>)",
        ));
    }
    let registry = parse_and_install_dialect(&items[0])?;
    let d = leaf(&registry)?;
    let message =
        crate::parse_message(&items[1]).map_err(|e| format!("message parse error: {e}"))?;
    match cbcl_core::r7::verify_state_shape(&d, &message) {
        Ok(()) => Ok(String::from("ok")),
        Err(v) => {
            let blame =
                ViolationError::from_shape_violation(&v, None, None, Some(items[1].clone()))
                    .with_dialect_context(&d.name, d.author.as_deref(), d.hash.as_deref(), None);
            Err(serialize(&blame.to_sexpr()))
        }
    }
}

/// `(state-schema <dialect>)` → the schema as JSON.
pub fn state_schema_str(input: &str) -> Result<String, String> {
    let items = parse_frame(input, "state-schema")?;
    if items.len() != 1 {
        return Err(String::from("expected (state-schema <dialect>)"));
    }
    let registry = parse_and_install_dialect(&items[0])?;
    let d = leaf(&registry)?;
    let clause = d
        .state
        .as_ref()
        .ok_or_else(|| String::from("dialect has no state clause"))?;
    Ok(render_schema(&state_schema(clause, &d.shapes)))
}

/// `(may-send <dialect> <thread> (acts …) <signer>)` → a JSON array of verbs.
pub fn may_send_str(input: &str) -> Result<String, String> {
    let (d, thread, acts, rest) = instance_frame(input, "may-send")?;
    if rest.len() != 1 {
        return Err(String::from(
            "expected (may-send <dialect> <thread> (acts …) <signer>)",
        ));
    }
    let signer = AgentKey(atom_text(&rest[0], "signer")?);
    let inst = Instance::new(&d, thread, &acts)?;
    Ok(Value::Set(
        may_send(&inst, &signer)
            .into_iter()
            .map(Value::Str)
            .collect(),
    )
    .render())
}

/// `(frontier <dialect> <thread> (acts …))` → `{"instance":…,"frontier":[…]}`.
pub fn frontier_str(input: &str) -> Result<String, String> {
    let (d, thread, acts, _) = instance_frame(input, "frontier")?;
    let inst = Instance::new(&d, thread, &acts)?;
    let instance = match inst.instance_id() {
        Some(a) => Value::Str(String::from(a)),
        None => Value::Absent,
    };
    let f = Value::List(frontier(&acts).into_iter().map(Value::Str).collect());
    Ok(format!(
        "{{\"instance\":{},\"frontier\":{}}}",
        instance.render(),
        f.render()
    ))
}

/// One message's admission verdict against an accepted set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Admission {
    /// Shape-valid and causally valid against the accepted set.
    Accepted,
    /// Shape-valid; a predecessor it names is not yet accepted (retry as the
    /// set grows).
    Pending,
    /// Blamed on the sender, with the reason.
    Rejected(String),
}

/// Admission as a consumer runs it (SPEC-019 R.4; SPEC-002 R5; SPEC-014 R6):
/// the shape stage judges the message alone (R5 shape, R7 state shape); the
/// causal stage judges it against the accepted set of its thread, under the
/// cast when the thread has an accepted root, and is `Pending` while a
/// predecessor is missing. `accepted` is the accepted set so far; the caller
/// retries `Pending` messages as it grows. One implementation for every
/// binding and for the corpus runner, so the accepted set a consumer folds is
/// the one the corpus expects.
pub fn admit(d: &Dialect, thread: &ThreadId, accepted: &[Act], act: &Act) -> Admission {
    let Some(protocol) = d.causal_protocol.as_ref() else {
        return Admission::Rejected(String::from("dialect has no protocol clause"));
    };
    if let Err(v) = cbcl_core::r7::verify_state_shape(d, &act.message) {
        return Admission::Rejected(format!("state shape: {v}"));
    }
    for shape in d.shapes.iter().filter(|s| s.performative == act.verb) {
        if let Err(v) = shape.check(&SExpr::from(act.simple())) {
            return Admission::Rejected(format!("shape: {v}"));
        }
    }
    let inst = match Instance::new(d, thread.clone(), accepted) {
        Ok(i) => i,
        Err(e) => return Admission::Rejected(e),
    };
    let mut store = inst.store();
    store.append(
        ContentHash(act.address.clone()),
        thread.clone(),
        act.message.clone(),
    );
    let endpoint = Endpoint {
        role: String::new(),
        occupant: Some(AgentKey(act.signer.clone())),
    };
    let verdict = match (&inst.cast, inst.root) {
        (Some(cast), Some(root)) => verify_causal_for_role(
            &act.message,
            &endpoint,
            d,
            cast,
            &store,
            thread,
            &ContentHash(root.address.clone()),
        ),
        _ if d.roles.is_empty() => verify_causal(
            &act.verb,
            act.simple().caused_by(),
            &store,
            protocol,
            thread,
        ),
        // A role-declaring dialect with no accepted root yet: only the root
        // itself, which carries its own cast, can be judged.
        _ if act.predecessors.is_empty() => match cast_of(&act.message, d) {
            Ok(cast) => verify_causal_for_role(
                &act.message,
                &endpoint,
                d,
                &cast,
                &store,
                thread,
                &ContentHash(act.address.clone()),
            ),
            Err(e) => return Admission::Rejected(format!("root: {e}")),
        },
        _ => VerificationResult::Unknown,
    };
    match verdict {
        VerificationResult::Valid => Admission::Accepted,
        VerificationResult::Unknown => Admission::Pending,
        VerificationResult::Violation(v) => Admission::Rejected(format!("{v}")),
    }
}

/// `(admit <dialect> <thread> (acts …) (<signer> <message>))` → JSON
/// `{"verdict":"accepted"}`, `{"verdict":"pending"}`, or
/// `{"verdict":"rejected","reason":…}`. The acts are the accepted set so far.
pub fn admit_str(input: &str) -> Result<String, String> {
    let (d, thread, accepted, rest) = instance_frame(input, "admit")?;
    if rest.len() != 1 {
        return Err(String::from(
            "expected (admit <dialect> <thread> (acts …) (<signer> <message>))",
        ));
    }
    let one = SExpr::List(alloc::vec![
        SExpr::Atom(Atom::Symbol(String::from("acts"))),
        rest[0].clone(),
    ]);
    let mut acts = parse_acts(&one)?;
    let act = acts
        .pop()
        .ok_or_else(|| String::from("expected (<signer> <message>)"))?;
    Ok(match admit(&d, &thread, &accepted, &act) {
        Admission::Accepted => String::from("{\"verdict\":\"accepted\"}"),
        Admission::Pending => String::from("{\"verdict\":\"pending\"}"),
        Admission::Rejected(reason) => format!(
            "{{\"verdict\":\"rejected\",\"reason\":{}}}",
            Value::Str(reason).render()
        ),
    })
}

/// A `(define …)` → its self-addressed name `sha256-<hex>` (SPEC-019 R.6).
pub fn dialect_hash_str(input: &str) -> Result<String, String> {
    let sexpr = crate::parser::parse(input).map_err(|e| format!("parse error: {e}"))?;
    let d = crate::parse_dialect(&sexpr).map_err(|e| format!("dialect parse error: {e}"))?;
    Ok(dialect_name(&d))
}
