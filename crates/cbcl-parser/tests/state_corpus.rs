//! SPEC-019 conformance corpus runner (REQ-1931, CON-1904, TEST-1931).
//!
//! Each vector in `test-vectors/state/*.json` carries a dialect, a list of
//! signed canonical messages, and the expected addresses, verdicts, and
//! state. The runner feeds the messages forward, reversed, and duplicated,
//! and expects identical state each time. Vectors may also carry intents
//! with the canonical act the binder must produce, or the rejection it
//! must return.
//!
//! Set `STATE_CORPUS_PRINT=1` to print each vector's computed expectation
//! (used to author a vector: fill `messages`, run, paste `expect`).

use cbcl_core::dialect::Dialect;
use cbcl_core::intend::{intend, Instance};
use cbcl_core::role::AgentKey;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::state::{fold, render_json, Act};
use cbcl_core::store::ThreadId;
use cbcl_parser::state_exports::{self, Admission};
use cbcl_parser::{parse, parse_dialect, parse_message};
use serde_json::{json, Map, Value};
use std::collections::BTreeMap;
use std::path::PathBuf;

fn corpus_dir() -> PathBuf {
    PathBuf::from(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../test-vectors/state"
    ))
}

fn json_to_sexpr(v: &Value) -> SExpr {
    match v {
        Value::String(s) => SExpr::Atom(Atom::Str(s.clone())),
        Value::Number(n) => SExpr::Atom(Atom::Num(n.as_i64().expect("integer"))),
        Value::Bool(b) => SExpr::Atom(Atom::Bool(*b)),
        Value::Array(items) => SExpr::List(items.iter().map(json_to_sexpr).collect()),
        other => panic!("unsupported field value {other}"),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Accepted,
    Rejected,
    Pending,
}

/// Admission as a consumer runs it: the shared `state_exports::admit` per
/// message, retried while pending as the accepted set grows.
fn admit(
    d: &Dialect,
    thread: &ThreadId,
    messages: &[(String, String)],
) -> (Vec<(String, Verdict)>, Vec<Act>) {
    let mut acts: Vec<Act> = Vec::new();
    let mut verdicts: Vec<Verdict> = Vec::new();
    let mut addresses: Vec<String> = Vec::new();
    for (canonical, signer) in messages {
        let message = parse_message(&parse(canonical).unwrap()).unwrap();
        let act = Act::from_message(message, signer).unwrap();
        addresses.push(act.address.clone());
        acts.push(act);
        verdicts.push(Verdict::Pending);
    }
    let mut accepted: Vec<Act> = Vec::new();
    loop {
        let mut progressed = false;
        for i in 0..acts.len() {
            if verdicts[i] != Verdict::Pending {
                continue;
            }
            match state_exports::admit(d, thread, &accepted, &acts[i]) {
                Admission::Accepted => {
                    verdicts[i] = Verdict::Accepted;
                    // A re-delivered act is the same act (REQ-1920).
                    if !accepted.iter().any(|a| a.address == acts[i].address) {
                        accepted.push(acts[i].clone());
                    }
                    progressed = true;
                }
                Admission::Rejected(_) => {
                    verdicts[i] = Verdict::Rejected;
                    progressed = true;
                }
                Admission::Pending => {}
            }
        }
        if !progressed {
            break;
        }
    }
    (addresses.into_iter().zip(verdicts).collect(), accepted)
}

fn verdict_name(v: Verdict) -> &'static str {
    match v {
        Verdict::Accepted => "accepted",
        Verdict::Rejected => "rejected",
        Verdict::Pending => "pending",
    }
}

fn run_vector(path: &PathBuf) {
    let text = std::fs::read_to_string(path).unwrap();
    let vector: Value = serde_json::from_str(&text).unwrap();
    let id = vector["id"].as_str().unwrap();
    let d = parse_dialect(&parse(vector["contract"].as_str().unwrap()).unwrap())
        .unwrap_or_else(|e| panic!("{id}: contract: {e}"));
    let thread = ThreadId(vector["thread"].as_str().unwrap_or("t").to_string());
    let messages: Vec<(String, String)> = vector["messages"]
        .as_array()
        .unwrap()
        .iter()
        .map(|m| {
            (
                m["canonical"].as_str().unwrap().to_string(),
                m["signer"].as_str().unwrap().to_string(),
            )
        })
        .collect();
    let clause = d.state.as_ref().expect("state clause");

    let (verdicts, accepted) = admit(&d, &thread, &messages);
    let state = render_json(&fold(clause, d.causal_protocol.as_ref(), &accepted));

    // Reversed and duplicated deliveries give the same state.
    let mut reversed = messages.clone();
    reversed.reverse();
    let (_, acc_rev) = admit(&d, &thread, &reversed);
    assert_eq!(
        render_json(&fold(clause, d.causal_protocol.as_ref(), &acc_rev)),
        state,
        "{id}: reversed delivery"
    );
    let mut duplicated = messages.clone();
    duplicated.extend(messages.iter().cloned());
    let (_, acc_dup) = admit(&d, &thread, &duplicated);
    let mut dedup: Vec<Act> = Vec::new();
    for a in acc_dup {
        if !dedup.iter().any(|x| x.address == a.address) {
            dedup.push(a);
        }
    }
    assert_eq!(
        render_json(&fold(clause, d.causal_protocol.as_ref(), &dedup)),
        state,
        "{id}: duplicated delivery"
    );

    // Intents.
    let mut intent_results: Vec<Value> = Vec::new();
    if let Some(intents) = vector["intents"].as_array() {
        let inst = Instance::new(&d, thread.clone(), &accepted).unwrap();
        for it in intents {
            let signer = AgentKey(it["signer"].as_str().unwrap().to_string());
            let verb = it["verb"].as_str().unwrap();
            let fields: BTreeMap<String, SExpr> = it["fields"]
                .as_object()
                .map(|o| {
                    o.iter()
                        .map(|(k, v)| (k.clone(), json_to_sexpr(v)))
                        .collect()
                })
                .unwrap_or_default();
            let result = match intend(&inst, &signer, verb, fields) {
                Ok(m) => json!({ "canonical": cbcl_core::intend::canonical_text(&m) }),
                Err(r) => json!({ "reject": r.kind() }),
            };
            intent_results.push(result);
        }
    }

    let mut verdict_map = Map::new();
    for (a, v) in &verdicts {
        verdict_map.insert(a.clone(), Value::String(verdict_name(*v).to_string()));
    }
    let computed = json!({
        "addresses": verdicts.iter().map(|(a, _)| a.clone()).collect::<Vec<_>>(),
        "verdicts": Value::Object(verdict_map),
        "state": serde_json::from_str::<Value>(&state).unwrap(),
        "intents": intent_results,
    });
    if std::env::var("STATE_CORPUS_PRINT").is_ok() {
        println!("{id}: {}", serde_json::to_string_pretty(&computed).unwrap());
    }

    if std::env::var("STATE_CORPUS_WRITE").is_ok() {
        let mut updated = vector.clone();
        updated["expect"] = computed.clone();
        std::fs::write(path, serde_json::to_string_pretty(&updated).unwrap() + "\n").unwrap();
        return;
    }
    let expect = &vector["expect"];
    if expect.is_null() {
        panic!("{id}: no expect member; run once with STATE_CORPUS_WRITE=1 to author it");
    }
    assert_eq!(
        computed["addresses"], expect["addresses"],
        "{id}: addresses"
    );
    assert_eq!(computed["verdicts"], expect["verdicts"], "{id}: verdicts");
    assert_eq!(computed["state"], expect["state"], "{id}: state");
    if !expect["intents"].is_null() {
        assert_eq!(computed["intents"], expect["intents"], "{id}: intents");
    }
}

#[test]
fn every_vector_passes_forward_reversed_and_duplicated() {
    let dir = corpus_dir();
    assert_eq!(
        std::fs::read_to_string(dir.join("VERSION")).unwrap().trim(),
        "1.0.0",
        "state corpus version is pinned"
    );
    let mut paths: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "json"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "no vectors in {}", dir.display());
    for p in &paths {
        run_vector(p);
    }
}
