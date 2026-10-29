//! Native admission/fold oracle for the recursive o1js experiment fixtures.
use cbcl_core::{
    dialect::Dialect,
    message::Message,
    serializer::serialize,
    sexpr::{Atom, SExpr},
    state::{fold, render_json, Act},
    store::ThreadId,
};
use cbcl_parser::{
    compile_contract_str, parse, parse_and_install_dialect, parse_message,
    state_exports::{admit, Admission},
};
use serde::Deserialize;
use serde_json::{json, Value};
use std::io::{self, Read};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Input {
    records: Vec<Record>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Record {
    nonce: u32,
    amount: u32,
    author: bool,
}
fn symbol(text: &str) -> SExpr {
    SExpr::Atom(Atom::Symbol(text.into()))
}
fn message(
    name: &str,
    verb: &str,
    from: &str,
    cause: &str,
    fields: Vec<(&str, SExpr)>,
) -> Result<Message, String> {
    let mut inner = vec![symbol(verb), symbol("@room")];
    for (k, v) in fields.into_iter().chain([
        ("from", symbol(from)),
        ("thread", SExpr::Atom(Atom::Str("recursive-counter".into()))),
        ("caused-by", symbol(cause)),
    ]) {
        inner.push(SExpr::Atom(Atom::Keyword(k.into())));
        inner.push(v);
    }
    parse_message(&SExpr::List(vec![
        symbol("lang"),
        symbol(name),
        SExpr::List(inner),
    ]))
    .map_err(|e| e.to_string())
}
fn main() -> Result<(), String> {
    let mut bytes = Vec::new();
    io::stdin()
        .take(8193)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.len() > 8192 {
        return Err("input too large".into());
    }
    let input: Input = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
    if input.records.len() > 4 || input.records.iter().any(|r| r.amount == 0) {
        return Err("experiment profile bound".into());
    }
    let contract = json!({"version":3,"kind":"contract","name":"recursive-contributions", "verbs":{
        "open":{"after":["begin"],"fields":{"title":"string"}},
        "contribute":{"after":["open"],"fields":{"nonce":"number","amount":"number"}}
    },"state":{"contributions":["events","contribute","amount"],"total":["sum","contributions"],"count":["count","contribute"]}});
    let compiled: Value = serde_json::from_str(&compile_contract_str(&contract.to_string())?)
        .map_err(|e| e.to_string())?;
    let source = compiled["dialect"].as_str().ok_or("missing dialect")?;
    let registry = parse_and_install_dialect(&parse(source).map_err(|e| e.to_string())?)?;
    let d: &Dialect = registry.iter().last().ok_or("missing dialect")?;
    let root = Act::from_message(
        message(
            &d.name,
            "open",
            "@alice",
            "begin",
            vec![(
                "title",
                SExpr::Atom(Atom::Str("Recursive proof experiment".into())),
            )],
        )?,
        "@alice",
    )?;
    let object = root.address.clone();
    let thread = ThreadId("recursive-counter".into());
    let mut accepted = Vec::new();
    if admit(d, &thread, &accepted, &root) != Admission::Accepted {
        return Err("opener not admitted".into());
    }
    accepted.push(root);
    for record in input.records {
        let signer = if record.author { "@bob" } else { "@alice" };
        let act = Act::from_message(
            message(
                &d.name,
                "contribute",
                signer,
                &object,
                vec![
                    ("nonce", SExpr::Atom(Atom::Num(record.nonce.into()))),
                    ("amount", SExpr::Atom(Atom::Num(record.amount.into()))),
                ],
            )?,
            signer,
        )?;
        if accepted.iter().any(|a| a.address == act.address) {
            continue;
        }
        if admit(d, &thread, &accepted, &act) != Admission::Accepted {
            return Err("contribution not admitted".into());
        }
        accepted.push(act);
    }
    let state = render_json(&fold(
        d.state.as_ref().ok_or("missing state")?,
        d.causal_protocol.as_ref(),
        &accepted,
    ));
    println!(
        "{}",
        json!({"dialect":d.name,"opener":object,"thread":thread.0,"state":serde_json::from_str::<Value>(&state).map_err(|e|e.to_string())?,"messages":accepted.iter().map(|a|json!({"address":a.address,"canonical":serialize(&SExpr::from(&a.message)),"signer":a.signer})).collect::<Vec<_>>()})
    );
    Ok(())
}
