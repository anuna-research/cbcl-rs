//! The messages shown in `docs/concepts/example-coin.md` are real: each lisp
//! block is parsed from the document itself, its content address is checked
//! against `test-vectors/state/bounded-coin.json`, the fold is checked, and the
//! documented `intend` call must reproduce the documented `pay` act.
use cbcl_core::intend::{intend, Instance};
use cbcl_core::role::AgentKey;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::state::{fold, render_json, Act};
use cbcl_core::store::ThreadId;
use cbcl_parser::{parse, parse_dialect, parse_message};
use std::collections::BTreeMap;

const DOC: &str = include_str!("../../../docs/concepts/example-coin.md");
const COIN: &str = include_str!("../../../dialects/example-coin.cbcl");

const ROOT_ADDR: &str = "f122067bb33cf1e30749bc9175826525393ce0a0f4a45315c94338714edb31a8849c6";
const OPEN_ADDR: &str = "f1220400baa8fa18604fedff1606554d3d3fc922b89391f627640a4d7a749ba482963";
const PAY_ADDR: &str = "f1220de5e5d7d66a0e12c00785cbeb8e6fe12b851c5b4f3c45596e702622532be70b2";

/// Every fenced block in the document tagged with `lang`, in order.
fn blocks(lang: &str) -> Vec<String> {
    let fence = format!("```{lang}\n");
    DOC.split(&fence)
        .skip(1)
        .map(|rest| rest.split("```").next().unwrap().to_string())
        .collect()
}

fn act(source: &str, signer: &str) -> Act {
    Act::from_message(parse_message(&parse(source).unwrap()).unwrap(), signer).unwrap()
}

#[test]
fn documented_messages_parse_address_and_fold_as_claimed() {
    let lisp = blocks("lisp");
    assert_eq!(lisp.len(), 4, "dialect, root, open, pay");
    assert_eq!(
        lisp[0].trim(),
        COIN.trim(),
        "README quotes the dialect verbatim"
    );

    let dialect = parse_dialect(&parse(&lisp[0]).unwrap()).unwrap();
    let mut registry = cbcl_core::dialect::DialectRegistry::new();
    registry.install(dialect.clone()).unwrap();

    let root = act(&lisp[1], "@treasury");
    let open = act(&lisp[2], "@treasury");
    let pay = act(&lisp[3], "@treasury");
    assert_eq!(
        root.address, ROOT_ADDR,
        "root address matches the test vector"
    );
    assert_eq!(
        open.address, OPEN_ADDR,
        "open address matches the test vector"
    );
    assert_eq!(pay.address, PAY_ADDR, "pay address matches the test vector");
    assert_eq!(
        open.predecessors,
        vec![ROOT_ADDR.to_string()],
        "open cites the root"
    );
    assert_eq!(
        pay.predecessors,
        vec![OPEN_ADDR.to_string()],
        "pay cites open"
    );

    let acts = vec![root.clone(), open.clone(), pay.clone()];
    let state: serde_json::Value = serde_json::from_str(&render_json(&fold(
        dialect.state.as_ref().unwrap(),
        dialect.causal_protocol.as_ref(),
        &acts,
    )))
    .unwrap();
    assert_eq!(state["name"], "Example Coin");
    assert_eq!(state["coins"]["status"], "ready");
    assert_eq!(state["coins"]["value"], 1000);
    assert_eq!(state["coins"]["rights"]["@treasury"], 900);
    assert_eq!(state["coins"]["rights"]["@alice"], 100);
    assert_eq!(state["coins"]["rights"]["@bob"], 0);

    // The documented `intend` call reproduces the documented pay act exactly.
    let accepted = vec![root, open];
    let inst = Instance::new(&dialect, ThreadId("coin-1".into()), &accepted).unwrap();
    let fields = BTreeMap::from([
        (
            "recipient".to_string(),
            SExpr::Atom(Atom::Symbol("@alice".into())),
        ),
        ("amount".to_string(), SExpr::Atom(Atom::Num(100))),
    ]);
    let built = intend(&inst, &AgentKey("@treasury".into()), "pay", fields).unwrap();
    let built = Act::from_message(built, "@treasury").unwrap();
    assert_eq!(
        built.address, pay.address,
        "intend output equals the documented pay act"
    );
    assert_eq!(built.fields, pay.fields);
}
