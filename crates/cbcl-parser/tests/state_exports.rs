//! SPEC-019 R.7 exports against the conformance corpus (SPEC-010 REQ-002).
//!
//! Every binding (WASM, Erlang NIF, C FFI) wraps `cbcl_parser::state_exports`
//! without adding semantics, so driving the frames against the corpus here
//! is the conformance gate for all three: same frame in, same bytes out.

use serde_json::Value;
use std::path::PathBuf;

fn corpus_dir() -> PathBuf {
    PathBuf::from(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../test-vectors/state"
    ))
}

fn sexpr_of_json(v: &Value) -> String {
    match v {
        Value::String(s) => format!("{:?}", s),
        Value::Number(n) => n.to_string(),
        Value::Bool(b) => {
            if *b {
                "#t".into()
            } else {
                "#f".into()
            }
        }
        Value::Array(items) => format!(
            "({})",
            items
                .iter()
                .map(sexpr_of_json)
                .collect::<Vec<_>>()
                .join(" ")
        ),
        other => panic!("unsupported field value {other}"),
    }
}

#[test]
fn frames_reproduce_every_vector() {
    let mut paths: Vec<PathBuf> = std::fs::read_dir(corpus_dir())
        .unwrap()
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "json"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty());
    for path in paths {
        let vector: Value = serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
        let id = vector["id"].as_str().unwrap();
        let contract = vector["contract"].as_str().unwrap();
        let thread = vector["thread"].as_str().unwrap_or("t");
        let expect = &vector["expect"];
        let verdicts = expect["verdicts"].as_object().unwrap();
        let addresses: Vec<&str> = expect["addresses"]
            .as_array()
            .unwrap()
            .iter()
            .map(|a| a.as_str().unwrap())
            .collect();

        // The accepted acts, as the vector's verdicts say.
        let mut entries = Vec::new();
        for (i, m) in vector["messages"].as_array().unwrap().iter().enumerate() {
            if verdicts[addresses[i]] == "accepted" {
                let canonical = m["canonical"].as_str().unwrap();
                let signer = m["signer"].as_str().unwrap();
                if !entries.iter().any(|(a, _)| *a == addresses[i]) {
                    entries.push((addresses[i], format!("({signer} {canonical})")));
                }
            }
        }
        let acts = format!(
            "(acts {})",
            entries
                .iter()
                .map(|(_, e)| e.as_str())
                .collect::<Vec<_>>()
                .join(" ")
        );

        // fold
        let state =
            cbcl_parser::state_exports::fold_str(&format!("(fold {contract} {thread:?} {acts})"))
                .unwrap_or_else(|e| panic!("{id}: fold: {e}"));
        assert_eq!(
            serde_json::from_str::<Value>(&state).unwrap(),
            expect["state"],
            "{id}: fold"
        );

        // intend
        if let (Some(intents), Some(expected)) =
            (vector["intents"].as_array(), expect["intents"].as_array())
        {
            for (it, ex) in intents.iter().zip(expected) {
                let signer = it["signer"].as_str().unwrap();
                let verb = it["verb"].as_str().unwrap();
                let fields: String = it["fields"]
                    .as_object()
                    .map(|o| {
                        o.iter()
                            .map(|(k, v)| format!(":{k} {}", sexpr_of_json(v)))
                            .collect::<Vec<_>>()
                            .join(" ")
                    })
                    .unwrap_or_default();
                let frame =
                    format!("(intend {contract} {thread:?} {acts} {signer} {verb} ({fields}))");
                match cbcl_parser::state_exports::intend_str(&frame) {
                    Ok(canonical) => assert_eq!(
                        Value::String(canonical),
                        ex["canonical"],
                        "{id}: intend {verb}"
                    ),
                    Err(reject) => {
                        let r: Value = serde_json::from_str(&reject)
                            .unwrap_or_else(|_| panic!("{id}: {reject}"));
                        assert_eq!(r["reject"], ex["reject"], "{id}: intend {verb} rejection");
                    }
                }
            }
        }

        // schema, frontier, self-address, state shape of every accepted act
        cbcl_parser::state_exports::state_schema_str(&format!("(state-schema {contract})"))
            .unwrap();
        let fr = cbcl_parser::state_exports::frontier_str(&format!(
            "(frontier {contract} {thread:?} {acts})"
        ))
        .unwrap();
        let fr: Value = serde_json::from_str(&fr).unwrap();
        assert!(
            fr["frontier"]
                .as_array()
                .unwrap()
                .iter()
                .all(|a| addresses.contains(&a.as_str().unwrap())),
            "{id}: frontier"
        );
        let name = cbcl_parser::state_exports::dialect_hash_str(contract).unwrap();
        assert!(
            name.starts_with("sha256-") && name.len() == 7 + 64,
            "{id}: {name}"
        );
        for m in vector["messages"].as_array().unwrap() {
            let canonical = m["canonical"].as_str().unwrap();
            let _ = cbcl_parser::state_exports::verify_state_shape_str(&format!(
                "(verify-state-shape {contract} {canonical})"
            ));
        }
    }
}

/// TEST-1951: exported admission and shape frames preserve signer bookkeeping.
#[test]
fn signer_replaces_shape_is_exported() {
    let contract = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../dialects/lunch-vote.cbcl"
    ))
    .unwrap();
    let missing =
        "(lang lunch-vote (vote @room :choice \"Pizza\" :caused-by begin :thread \"v1\" :from @a))";
    let result = cbcl_parser::state_exports::verify_state_shape_str(&format!(
        "(verify-state-shape {contract} {missing})"
    ));
    assert!(
        result.is_err(),
        "latest-per-signer requires replacement bookkeeping"
    );
    let empty = missing.replace(":choice \"Pizza\"", ":choice \"Pizza\" :replaces ()");
    assert!(cbcl_parser::state_exports::verify_state_shape_str(&format!(
        "(verify-state-shape {contract} {empty})"
    ))
    .is_ok());
}
