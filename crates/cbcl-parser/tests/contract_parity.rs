//! SPEC-087 TEST-001: a JSON contract compiles to exactly the dialect an
//! author would write by hand, byte-for-byte in identity (the self-address),
//! and TEST-002: recognition and R1–R7 refuse what they should.

use cbcl_core::canonical::dialect_name;
use cbcl_parser::{compile_contract_str, parse, parse_dialect};
use serde_json::{json, Value};
use std::path::PathBuf;

fn authored(file: &str) -> String {
    let path = PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../../dialects/")).join(file);
    let text = std::fs::read_to_string(&path).unwrap();
    dialect_name(&parse_dialect(&parse(&text).unwrap()).unwrap())
}

fn compiled(contract: &Value) -> Value {
    serde_json::from_str(&compile_contract_str(&contract.to_string()).unwrap()).unwrap()
}

fn checklist() -> Value {
    json!({"version":3,"kind":"contract","name":"checklist","author":"@anuna",
      "roles":{"owner":"singleton","member":"indexed"},
      "verbs":{
        "open":{"after":["begin"],"fields":{"title":"string"},"from":"owner","to":["owner","member"]},
        "check":{"after":["open"],"fields":{"item":"string","done":"bool"},"from":"member","to":["owner","member"]},
        "drop":{"after":["open"],"fields":{"item":"string"},"from":"owner","to":["owner","member"]}},
      "state":{"title":["last","open","title"],"items":["registerPerKey","check","item","done","drop"]}})
}

fn lunch_vote() -> Value {
    json!({"version":3,"kind":"contract","name":"lunch-vote","author":"@anuna",
      "requirements":{"maxDepth":12,"maxExpansionSize":2048,"verificationTime":200},
      "bounds":{"maxString":280,"maxList":24},
      "verbs":{
        "propose":{"after":["begin"],"fields":{"question":"string","options":"list"}},
        "vote":{"after":["propose"],"fields":{"choice":{"enumOf":"options"}}}},
      "state":{"question":["last","propose","question"],"options":["last","propose","options"],
               "ballots":["latestPerSigner","vote","choice"],"tally":["histogram","ballots"]}})
}

#[test]
fn checklist_and_lunch_vote_compile_to_the_authored_dialects() {
    for (contract, file) in [(checklist(), "checklist.cbcl"), (lunch_vote(), "lunch-vote.cbcl")] {
        let out = compiled(&contract);
        assert_eq!(out["name"], authored(file), "{file}");
        assert_eq!(out["label"], contract["name"]);
        let text = out["dialect"].as_str().unwrap();
        assert!(text.starts_with(&format!("(define {} (cbcl) @anuna", out["name"].as_str().unwrap())));
        assert_eq!(dialect_name(&parse_dialect(&parse(text).unwrap()).unwrap()), out["name"]);
    }
}

#[test]
fn identity_is_the_body_and_the_state_clause_is_part_of_it() {
    let a = compiled(&checklist());
    let mut relabelled = checklist();
    relabelled["name"] = json!("another-label");
    assert_eq!(compiled(&relabelled)["name"], a["name"]);
    let mut smaller = checklist();
    smaller["state"] = json!({"title":["last","open","title"]});
    assert_ne!(compiled(&smaller)["name"], a["name"]);
    let text = a["dialect"].as_str().unwrap();
    assert!(text.contains("(state (title (last open :title)) (items (register-per-key check :item :done drop)))"));
    assert!(text.contains("(:roles (owner (* member)))"));
    assert!(text.contains("(extend check (to item done) :from member :to (owner member) (tell to :item item :done done))"));
    assert!(!text.contains("replaces"), "the compiler in cbcl-core, not the contract, inserts :replaces");
    let lunch = compiled(&lunch_vote());
    let text = lunch["dialect"].as_str().unwrap();
    assert!(text.contains("(options (last propose :options)) (domain vote :choice options) (ballots"));
    assert!(text.contains("(:state-bounds (max-string 280) (max-list 24))"));
    assert!(text.contains("(shape vote (require :choice string))"));
}

#[test]
fn recognition_and_verification_refuse_malformed_contracts() {
    let mutations: Vec<(&str, Box<dyn Fn(&mut Value)>)> = vec![
        ("unknown key", Box::new(|d| d["code"] = json!("alert(1)"))),
        ("executable rule", Box::new(|d| d["state"]["items"] = json!(["eval", "alert(1)"]))),
        ("routing field", Box::new(|d| d["verbs"]["check"]["fields"]["from"] = json!("string"))),
        ("reserved replaces", Box::new(|d| d["verbs"]["check"]["fields"]["replaces"] = json!("list"))),
        ("core verb", Box::new(|d| d["verbs"]["tell"] = json!({"after":["open"],"fields":{},"from":"owner","to":["owner"]}))),
        ("opener follows check", Box::new(|d| d["verbs"]["open"]["after"] = json!(["check"]))),
        ("unknown predecessor", Box::new(|d| d["verbs"]["check"]["after"] = json!(["missing"]))),
        ("nested histogram", Box::new(|d| d["state"]["tally"] = json!(["histogram", ["latestPerSigner", "check", "done"]]))),
        ("arity", Box::new(|d| d["state"]["items"] = json!(["registerPerKey", "check", "item"]))),
        ("domain to nowhere", Box::new(|d| d["verbs"]["check"]["fields"]["item"] = json!({"enumOf":"nowhere"}))),
        ("role kind", Box::new(|d| d["roles"] = json!({"owner":"one"}))),
        ("missing annotation", Box::new(|d| { d["verbs"]["check"].as_object_mut().unwrap().remove("from"); })),
        ("version", Box::new(|d| d["version"] = json!(2))),
        // cbcl-rs R5/R7 blame, not recognition:
        ("cycle", Box::new(|d| d["verbs"]["check"]["after"] = json!(["open", "check"]))),
        ("histogram over a scalar", Box::new(|d| d["state"]["tally"] = json!(["histogram", "title"]))),
        ("delete verb is the opener", Box::new(|d| d["state"]["items"] = json!(["registerPerKey", "check", "item", "done", "open"]))),
    ];
    for (why, mutate) in mutations {
        let mut d = checklist();
        mutate(&mut d);
        assert!(compile_contract_str(&d.to_string()).is_err(), "{why} should be refused");
    }
    assert!(compile_contract_str("{").unwrap_err().starts_with("contract:"));
    assert!(compile_contract_str(&"x".repeat(20000)).unwrap_err().contains("16 KiB"));
}
