//! Author the SPEC-019 conformance vectors (CON-1904) from the core itself.
//!
//! Ignored by default. Run once with
//! `cargo test -p cbcl-parser --test state_corpus_generate -- --ignored`
//! to (re)write the `messages` and `intents` of each vector, then
//! `STATE_CORPUS_WRITE=1 cargo test -p cbcl-parser --test state_corpus` to
//! fill each vector's `expect` from the runner, and finally the plain
//! runner to confirm. Addresses in `:caused-by` and `:replaces` are the
//! core's own, so a vector is only as right as the core; the point of the
//! corpus is that a second implementation must reproduce these exactly.

use cbcl_core::state::Act;
use cbcl_parser::{parse, parse_message};
use serde_json::{json, Value};
use std::path::PathBuf;

fn corpus_dir() -> PathBuf {
    PathBuf::from(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../test-vectors/state"
    ))
}

fn strip_comments(src: &str) -> String {
    src.lines()
        .filter(|l| !l.trim_start().starts_with(';'))
        .collect::<Vec<_>>()
        .join("\n")
        .trim()
        .to_string()
}

fn dialect_file(name: &str) -> String {
    strip_comments(
        &std::fs::read_to_string(format!(
            "{}/../../dialects/{name}",
            env!("CARGO_MANIFEST_DIR")
        ))
        .unwrap(),
    )
}

fn address(text: &str) -> String {
    Act::from_message(parse_message(&parse(text).unwrap()).unwrap(), "@x")
        .unwrap()
        .address
}

fn write(id: &str, vector: Value) {
    let path = corpus_dir().join(format!("{id}.json"));
    std::fs::create_dir_all(corpus_dir()).unwrap();
    std::fs::write(&path, serde_json::to_string_pretty(&vector).unwrap() + "\n").unwrap();
}

#[test]
#[ignore]
fn generate_checklist_with_roles() {
    let contract = dialect_file("checklist.cbcl");
    let n = "checklist";
    let m0 = "(with-roles ((owner @aria) (member @bo @cy)) (signed @aria (hello :thread \"list-1\" :caused-by begin)))".to_string();
    let a0 = address(&m0);
    let m1 = format!("(signed @aria (lang {n} (open (@aria @bo @cy) :title \"Launch tasks\" :caused-by {a0} :thread \"list-1\" :from @aria)))");
    let a1 = address(&m1);
    let m2 = format!("(signed @bo (lang {n} (check (@aria @bo @cy) :item \"venue\" :done #f :replaces () :caused-by {a1} :thread \"list-1\" :from @bo)))");
    let a2 = address(&m2);
    let m3 = format!("(signed @bo (lang {n} (check (@aria @bo @cy) :item \"venue\" :done #t :replaces ({a2}) :caused-by {a1} :thread \"list-1\" :from @bo)))");
    let a3 = address(&m3);
    // @cy writes concurrently with M3, having seen only M2: both stay current.
    let m4 = format!("(signed @cy (lang {n} (check (@aria @bo @cy) :item \"venue\" :done #f :replaces ({a2}) :caused-by {a1} :thread \"list-1\" :from @cy)))");
    let a4 = address(&m4);
    let m5 = format!("(signed @bo (lang {n} (check (@aria @bo @cy) :item \"cake\" :done #f :replaces () :caused-by {a1} :thread \"list-1\" :from @bo)))");
    // @aria drops "venue" having seen M3 only; @cy's M4 survives (edit beats a concurrent delete).
    let m6 = format!("(signed @aria (lang {n} (drop (@aria @bo @cy) :item \"venue\" :replaces ({a3}) :caused-by {a1} :thread \"list-1\" :from @aria)))");
    // Rejected: a member may not drop (R6); rejected: undeclared field (R7 closed); pending: unknown predecessor.
    let bad_role = format!("(signed @bo (lang {n} (drop (@aria @bo @cy) :item \"cake\" :replaces () :caused-by {a1} :thread \"list-1\" :from @bo)))");
    let bad_field = format!("(signed @bo (lang {n} (check (@aria @bo @cy) :item \"cake\" :done #t :note \"x\" :replaces () :caused-by {a1} :thread \"list-1\" :from @bo)))");
    let pending = format!("(signed @bo (lang {n} (check (@aria @bo @cy) :item \"cake\" :done #t :replaces () :caused-by sha256-{} :thread \"list-1\" :from @bo)))", "f".repeat(64));
    let messages = [
        (&m0, "@aria"),
        (&m1, "@aria"),
        (&m2, "@bo"),
        (&m3, "@bo"),
        (&m4, "@cy"),
        (&m5, "@bo"),
        (&m6, "@aria"),
        (&bad_role, "@bo"),
        (&bad_field, "@bo"),
        (&pending, "@bo"),
    ];
    let _ = a4;
    write(
        "checklist-roles",
        json!({
            "id": "checklist-roles",
            "covers": ["last", "register-per-key", "delete-verb", "concurrent-writes", "add-wins-delete", "R6-role-gate", "R7-closed", "pending", "intend"],
            "thread": "list-1",
            "contract": contract,
            "messages": messages.iter().map(|(m, s)| json!({"canonical": m, "signer": s})).collect::<Vec<_>>(),
            "intents": [
                {"signer": "@bo", "verb": "check", "fields": {"item": "venue", "done": true}},
                {"signer": "@bo", "verb": "drop", "fields": {"item": "venue"}},
                {"signer": "@aria", "verb": "drop", "fields": {"item": "venue"}},
                {"signer": "@aria", "verb": "drop", "fields": {"item": "bread"}},
                {"signer": "@bo", "verb": "check", "fields": {"item": "venue", "done": true, "replaces": []}},
                {"signer": "@bo", "verb": "open", "fields": {"title": "again"}}
            ]
        }),
    );
}

#[test]
#[ignore]
fn generate_lunch_vote_domain() {
    let contract = dialect_file("lunch-vote.cbcl");
    let n = "lunch-vote";
    let p = format!("(lang {n} (propose @lunch :question \"Lunch?\" :options (\"Pizza\" \"Sushi\") :caused-by begin :thread \"v1\" :from @aria))");
    let a = address(&p);
    let v1 = format!(
        "(lang {n} (vote @lunch :choice \"Pizza\" :caused-by {a} :thread \"v1\" :from @bo))"
    );
    let v2 = format!(
        "(lang {n} (vote @lunch :choice \"Sushi\" :caused-by {a} :thread \"v1\" :from @bo))"
    );
    let v3 = format!(
        "(lang {n} (vote @lunch :choice \"Tacos\" :caused-by {a} :thread \"v1\" :from @cy))"
    );
    let v4 = format!(
        "(lang {n} (vote @lunch :choice \"Pizza\" :caused-by {a} :thread \"v1\" :from @dan))"
    );
    let long_q = "q".repeat(281);
    let too_long = format!("(lang {n} (propose @lunch :question \"{long_q}\" :options (\"a\") :caused-by begin :thread \"v1\" :from @eve))");
    let messages = [
        (&p, "@aria"),
        (&v1, "@bo"),
        (&v2, "@bo"),
        (&v3, "@cy"),
        (&v4, "@dan"),
        (&too_long, "@eve"),
    ];
    write(
        "lunch-vote-domain",
        json!({
            "id": "lunch-vote-domain",
            "covers": ["last", "latest-per-signer", "histogram", "domain", "state-bounds", "intend-domain"],
            "thread": "v1",
            "contract": contract,
            "messages": messages.iter().map(|(m, s)| json!({"canonical": m, "signer": s})).collect::<Vec<_>>(),
            "intents": [
                {"signer": "@dan", "verb": "vote", "fields": {"choice": "Sushi"}},
                {"signer": "@dan", "verb": "vote", "fields": {"choice": "Tacos"}}
            ]
        }),
    );
}

#[test]
#[ignore]
fn generate_tags_and_balance() {
    let contract = "(define tags (cbcl) @anuna
  (:resource-requirements ((max-depth 12) (max-expansion-size 2048) (verification-time 200)))
  (extend open (to title) (tell to :title title))
  (extend add (to tag op) (tell to :tag tag :op op))
  (extend remove (to tag) (tell to :tag tag))
  (extend credit (to amount op) (tell to :amount amount :op op))
  (extend debit (to amount op) (tell to :amount amount :op op))
  (shape open (require :title string))
  (shape add (require :tag string) (require :op string))
  (shape remove (require :tag string))
  (shape credit (require :amount number) (require :op string))
  (shape debit (require :amount number) (require :op string))
  (protocol (then begin open) (then open add) (then open remove) (then open credit) (then open debit))
  (state (title (last open :title))
         (tags (observed-set add remove :tag))
         (credits (events credit :amount))
         (total (sum credits))
         (balance (counter credit debit :amount))
         (adds (count add))))";
    let n = "tags";
    let o = format!(
        "(lang {n} (open @room :title \"Board\" :caused-by begin :thread \"b1\" :from @a))"
    );
    let ao = address(&o);
    let add1 = format!(
        "(lang {n} (add @room :tag \"urgent\" :op \"1\" :caused-by {ao} :thread \"b1\" :from @b))"
    );
    let a1 = address(&add1);
    let add2 = format!(
        "(lang {n} (add @room :tag \"urgent\" :op \"2\" :caused-by {ao} :thread \"b1\" :from @c))"
    );
    // A removal that saw only add1: add2 survives, so "urgent" stays.
    let rem1 = format!("(lang {n} (remove @room :tag \"urgent\" :replaces ({a1}) :caused-by {ao} :thread \"b1\" :from @a))");
    let add3 = format!(
        "(lang {n} (add @room :tag \"later\" :op \"3\" :caused-by {ao} :thread \"b1\" :from @b))"
    );
    let a3 = address(&add3);
    let rem2 = format!("(lang {n} (remove @room :tag \"later\" :replaces ({a3}) :caused-by {ao} :thread \"b1\" :from @c))");
    let c1 = format!(
        "(lang {n} (credit @room :amount 100 :op \"c1\" :caused-by {ao} :thread \"b1\" :from @a))"
    );
    let c2 = format!(
        "(lang {n} (credit @room :amount 250 :op \"c2\" :caused-by {ao} :thread \"b1\" :from @b))"
    );
    let d1 = format!(
        "(lang {n} (debit @room :amount 50 :op \"d1\" :caused-by {ao} :thread \"b1\" :from @a))"
    );
    let messages = [
        (&o, "@a"),
        (&add1, "@b"),
        (&add2, "@c"),
        (&rem1, "@a"),
        (&add3, "@b"),
        (&rem2, "@c"),
        (&c1, "@a"),
        (&c2, "@b"),
        (&d1, "@a"),
        (&c1, "@a"),
    ];
    write(
        "tags-and-balance",
        json!({
            "id": "tags-and-balance",
            "covers": ["observed-set", "add-wins", "events", "sum", "counter", "count", "duplicate-delivery", "intend-remove"],
            "thread": "b1",
            "contract": contract,
            "messages": messages.iter().map(|(m, s)| json!({"canonical": m, "signer": s})).collect::<Vec<_>>(),
            "intents": [
                {"signer": "@d", "verb": "remove", "fields": {"tag": "urgent"}},
                {"signer": "@d", "verb": "remove", "fields": {"tag": "gone"}},
                {"signer": "@d", "verb": "credit", "fields": {"amount": 5, "op": "c3"}}
            ]
        }),
    );
}
