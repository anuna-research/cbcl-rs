//! Synthetic native CBCL oracle for the authenticated-path register experiment.
use cbcl_core::{
    message::Message,
    serializer::serialize,
    sexpr::{Atom, SExpr},
    state::{fold, render_json, Act},
    store::ThreadId,
};
use cbcl_parser::{
    parse, parse_and_install_dialect, parse_message,
    state_exports::{admit, Admission},
};
use serde::Deserialize;
use serde_json::{json, Value};
use std::{
    collections::BTreeMap,
    io::{self, Read},
};

const SOURCE: &str = r#"(define incremental-register (cbcl) @anuna
  (extend open (to title) (tell to :title title))
  (extend write (to value op) (tell to :value value :op op))
  (shape open (require :title string))
  (shape write (require :value string) (require :op number))
  (protocol (then begin open) (then open write))
  (state (entries (latest-per-signer write :value)) (sequences (latest-per-signer write :op)) (all (events write :value))))"#;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Input {
    records: Vec<Record>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Record {
    signer: u32,
    seq: u32,
    value: u32,
    replaces: Option<String>,
}
fn symbol(s: &str) -> SExpr {
    SExpr::Atom(Atom::Symbol(s.into()))
}
fn message(
    verb: &str,
    signer: &str,
    cause: &str,
    fields: Vec<(&str, SExpr)>,
) -> Result<Message, String> {
    let mut inner = vec![symbol(verb), symbol("@room")];
    for (k, v) in fields.into_iter().chain([
        ("from", symbol(signer)),
        (
            "thread",
            SExpr::Atom(Atom::Str("incremental-register".into())),
        ),
        ("caused-by", symbol(cause)),
    ]) {
        inner.push(SExpr::Atom(Atom::Keyword(k.into())));
        inner.push(v);
    }
    parse_message(&SExpr::List(vec![
        symbol("lang"),
        symbol("incremental-register"),
        SExpr::List(inner),
    ]))
    .map_err(|e| e.to_string())
}
fn main() -> Result<(), String> {
    let mut bytes = Vec::new();
    io::stdin()
        .take(1_048_577)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.len() > 1_048_576 {
        return Err("input exceeds 1 MiB".into());
    }
    let value: Value = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
    let top = value.as_object().ok_or("expected input object")?;
    if let Some(Value::Array(records)) = top.get("records") {
        if records.iter().any(|r| !r.is_object()) {
            return Err("expected record objects".into());
        }
    }
    let input: Input = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
    if input.records.len() > 4096 || input.records.iter().any(|r| r.signer >= 65536) {
        return Err("experiment resource bound".into());
    }
    let registry = parse_and_install_dialect(&parse(SOURCE).map_err(|e| e.to_string())?)?;
    let dialect = registry.iter().last().ok_or("missing dialect")?;
    let root = Act::from_message(
        message(
            "open",
            "@owner",
            "begin",
            vec![(
                "title",
                SExpr::Atom(Atom::Str("Incremental register".into())),
            )],
        )?,
        "@owner",
    )?;
    let opener = root.address.clone();
    let thread = ThreadId("incremental-register".into());
    let mut accepted = vec![];
    if admit(dialect, &thread, &accepted, &root) != Admission::Accepted {
        return Err("opener not admitted".into());
    }
    accepted.push(root);
    let mut messages = vec![];
    let mut heads: BTreeMap<u32, String> = BTreeMap::new();
    for mut record in input.records {
        if record.replaces.as_deref() == Some("$head") {
            record.replaces = Some(
                heads
                    .get(&record.signer)
                    .ok_or("no prior generated head")?
                    .clone(),
            );
        }
        let signer = format!("@writer{}", record.signer);
        let replacements = record
            .replaces
            .as_ref()
            .map(|s| vec![symbol(s)])
            .unwrap_or_default();
        let act = Act::from_message(
            message(
                "write",
                &signer,
                &opener,
                vec![
                    ("value", SExpr::Atom(Atom::Str(record.value.to_string()))),
                    ("op", SExpr::Atom(Atom::Num(record.seq.into()))),
                    ("replaces", SExpr::List(replacements)),
                ],
            )?,
            &signer,
        )?;
        if admit(dialect, &thread, &accepted, &act) != Admission::Accepted {
            return Err("write not admitted".into());
        }
        messages.push(json!({"address":act.address,"canonical":serialize(&SExpr::from(&act.message)),"signer":record.signer,"seq":record.seq,"value":record.value,"replaces":record.replaces}));
        heads.insert(record.signer, act.address.clone());
        if !accepted.iter().any(|a| a.address == act.address) {
            accepted.push(act);
        }
    }
    let state = render_json(&fold(
        dialect.state.as_ref().ok_or("missing state")?,
        dialect.causal_protocol.as_ref(),
        &accepted,
    ));
    println!(
        "{}",
        json!({"source":SOURCE,"thread":thread.0,"opener":opener,"state":serde_json::from_str::<Value>(&state).map_err(|e|e.to_string())?,"messages":messages})
    );
    Ok(())
}
