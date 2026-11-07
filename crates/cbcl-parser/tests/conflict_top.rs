//! SPEC-038 TEST-3804: the conflict top. Two distinct openers render
//! `initial` as `{"status":"fault","evidence":[…]}` with both addresses; a
//! resource fork on a `bounded-counter` renders the same shape; in each case
//! the fault is sticky, surviving every superset of the accepted set with
//! evidence that still names the acts in conflict (REQ-3804, ADR-3803).
//!
//! The kernel is a function of the accepted set, so these tests feed acts to
//! `fold` directly. The late-write clause of TEST-3804 belongs to the freeze
//! task and is not covered here.
use cbcl_core::lattice::{factor, Ctx};
use cbcl_core::state::{fold, render_json, Act};
use cbcl_parser::{parse, parse_dialect, parse_message};
use serde_json::Value;

fn act(canonical: &str, signer: &str) -> Act {
    Act::from_message(parse_message(&parse(canonical).unwrap()).unwrap(), signer).unwrap()
}

fn state(contract: &str, acts: &[Act]) -> Value {
    let d = parse_dialect(&parse(contract).unwrap()).unwrap();
    let clause = d.state.as_ref().unwrap();
    serde_json::from_str(&render_json(&fold(
        clause,
        d.causal_protocol.as_ref(),
        acts,
    )))
    .unwrap()
}

/// The uniform conflict shape: `status` is `fault` and `evidence` is the
/// sorted list of the given addresses (REQ-3804).
fn assert_fault(field: &Value, addresses: &[&str]) {
    assert_eq!(field["status"], "fault", "status of {field}");
    let mut want: Vec<&str> = addresses.to_vec();
    want.sort();
    let got: Vec<&str> = field["evidence"]
        .as_array()
        .unwrap_or_else(|| panic!("evidence is not a list in {field}"))
        .iter()
        .map(|v| v.as_str().unwrap())
        .collect();
    assert_eq!(got, want, "evidence of {field}");
}

/// The fault names at least the original conflicting addresses.
fn assert_fault_covers(field: &Value, addresses: &[&str]) {
    assert_eq!(field["status"], "fault", "status of {field}");
    let got: Vec<&str> = field["evidence"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v.as_str().unwrap())
        .collect();
    for a in addresses {
        assert!(got.contains(a), "evidence of {field} lost {a}");
    }
    let mut sorted = got.clone();
    sorted.sort();
    assert_eq!(got, sorted, "evidence is sorted");
}

const OPENER_FORK: &str = "(define opener-fork (cbcl) @anuna \
  (extend open (to title) (tell to :title title)) \
  (extend note (to text) (tell to :text text)) \
  (shape open (require :title string)) \
  (shape note (require :text string)) \
  (protocol (then begin open) (then open note)) \
  (state (title (initial open :title)) (notes (count note))))";

fn open(title: &str, signer: &str) -> Act {
    act(
        &format!(
            "(lang opener-fork (open @room :title \"{title}\" :caused-by begin :thread \"t\" :from {signer}))"
        ),
        signer,
    )
}

fn note(text: &str, pred: &str, signer: &str) -> Act {
    act(
        &format!(
            "(lang opener-fork (note @room :text \"{text}\" :caused-by {pred} :thread \"t\" :from {signer}))"
        ),
        signer,
    )
}

#[test]
fn no_opener_is_absent_and_one_opener_is_its_value() {
    assert_eq!(state(OPENER_FORK, &[])["title"], Value::Null);
    let a = open("Alpha", "@a");
    assert_eq!(state(OPENER_FORK, &[a])["title"], "Alpha");
}

#[test]
fn two_distinct_openers_render_initial_as_fault_with_both_addresses() {
    let a = open("Alpha", "@a");
    let b = open("Beta", "@b");
    assert_ne!(a.address, b.address);
    let s = state(OPENER_FORK, &[a.clone(), b.clone()]);
    assert_fault(&s["title"], &[&a.address, &b.address]);
    // Exactly `evidence`, `reason` and `status`, the member set of the
    // bounded-counter resource fault: the shape is the same in every order.
    let mut sorted = vec![a.address.as_str(), b.address.as_str()];
    sorted.sort();
    assert_eq!(
        s["title"],
        serde_json::json!({"status": "fault", "reason": "opener fork", "evidence": sorted})
    );
    let rev = state(OPENER_FORK, &[b.clone(), a.clone()]);
    assert_eq!(rev["title"], s["title"], "order independence");
    let dup = state(OPENER_FORK, &[a.clone(), b.clone(), a.clone(), b]);
    assert_eq!(dup["title"], s["title"], "duplicate insensitivity");
}

#[test]
fn the_opener_fault_survives_every_superset() {
    let a = open("Alpha", "@a");
    let b = open("Beta", "@b");
    let c = open("Gamma", "@c");
    let n1 = note("after a", &a.address, "@a");
    let n2 = note("after b", &b.address, "@b");
    let original = [a.address.as_str(), b.address.as_str()];
    let conflicted = state(OPENER_FORK, &[a.clone(), b.clone()]);
    assert_fault(&conflicted["title"], &original);

    let supersets: Vec<Vec<Act>> = vec![
        vec![a.clone(), b.clone(), n1.clone()],
        vec![a.clone(), b.clone(), n1.clone(), n2.clone()],
        vec![a.clone(), b.clone(), c.clone()],
        vec![n2.clone(), c.clone(), b.clone(), n1.clone(), a.clone()],
    ];
    for acts in supersets {
        let s = state(OPENER_FORK, &acts);
        assert_fault_covers(&s["title"], &original);
        if acts.iter().any(|x| x.address == c.address) {
            assert_fault(&s["title"], &[&a.address, &b.address, &c.address]);
        } else {
            assert_fault(&s["title"], &original);
        }
    }
    // Other fields of the clause keep folding alongside the fault.
    let s = state(OPENER_FORK, &[a, b, n1, n2]);
    assert_eq!(s["notes"], 2);
}

/// The coin dialect of `test-vectors/state/bounded-coin.json`.
const COIN: &str = "(define example-coin (cbcl) @coin-author \
  (:resource-requirements ((max-depth 16) (max-expansion-size 4096) (verification-time 1000))) \
  (:roles (issuer (* holder))) \
  (extend open (to name allocations) :from issuer :to (issuer holder) (tell to :name name :allocations allocations)) \
  (extend mint (to amount) :from issuer :to (issuer holder) (tell to :amount amount)) \
  (extend burn (to amount) :from holder :to (issuer holder) (tell to :amount amount)) \
  (extend pay (to recipient amount) :from holder :to (issuer holder) (tell to :recipient recipient :amount amount)) \
  (shape open (require :name string) (require :allocations list)) \
  (shape mint (require :amount number)) \
  (shape burn (require :amount number)) \
  (shape pay (require :recipient symbol) (require :amount number)) \
  (protocol (then begin open) (then open mint) (then open burn) (then open pay)) \
  (state (name (initial open :name)) \
    (coins (bounded-counter (floor 0) (initial-rights open :allocations) (issuers issuer) \
      (increment mint :amount) (decrement burn :amount) (transfer pay :recipient :amount)))))";

const ROOT: &str = "(with-roles ((issuer @treasury) (holder @treasury @alice @bob)) (signed @treasury (hello () :thread \"coin-1\" :caused-by begin)))";

fn coin_open(root: &str) -> Act {
    act(
        &format!("(signed @treasury (lang example-coin (open (@alice @bob @treasury) () :name \"Example Coin\" :allocations ((@treasury 1000) (@alice 0) (@bob 0)) :from @treasury :thread \"coin-1\" :caused-by {root})))"),
        "@treasury",
    )
}

/// A transfer by `signer` whose escrow chain continues from `prev`.
fn pay(signer: &str, to: &str, amount: u32, prev: &str, deps: &str) -> Act {
    act(
        &format!("(signed {signer} (lang example-coin (pay (@alice @bob @treasury) () :amount {amount} :recipient {to} :escrow-prev {prev} :escrow-deps ({deps}) :from {signer} :thread \"coin-1\" :caused-by {prev})))"),
        signer,
    )
}

fn mint(amount: u32, prev: &str, deps: &str) -> Act {
    act(
        &format!("(signed @treasury (lang example-coin (mint (@alice @bob @treasury) () :amount {amount} :escrow-prev {prev} :escrow-deps ({deps}) :from @treasury :thread \"coin-1\" :caused-by {prev})))"),
        "@treasury",
    )
}

#[test]
fn a_resource_fork_renders_the_same_shape_and_survives_every_superset() {
    let root = act(ROOT, "@treasury");
    let open = coin_open(&root.address);
    let base = [root.clone(), open.clone()];
    let ready = state(COIN, &base);
    assert_eq!(ready["coins"]["status"], "ready");
    assert_eq!(ready["name"], "Example Coin");

    // Two transfers by one owner from the same escrow position: a fork.
    let p1 = pay("@treasury", "@alice", 100, &open.address, "");
    let p2 = pay("@treasury", "@bob", 50, &open.address, "");
    assert_ne!(p1.address, p2.address);
    let fork = [root.clone(), open.clone(), p1.clone(), p2.clone()];
    let s = state(COIN, &fork);
    assert_fault(
        &s["coins"],
        &[&root.address, &open.address, &p1.address, &p2.address],
    );
    let rev: Vec<Act> = fork.iter().rev().cloned().collect();
    assert_eq!(state(COIN, &rev)["coins"], s["coins"], "order independence");

    // Uniform with the opener fault: same members carry the same shape.
    let a = open_pair();
    let initial_fault = state(OPENER_FORK, &a)["title"].clone();
    assert_eq!(initial_fault["status"], s["coins"]["status"]);
    assert!(initial_fault["evidence"].is_array() && s["coins"]["evidence"].is_array());
    let members = |v: &Value| -> Vec<String> { v.as_object().unwrap().keys().cloned().collect() };
    assert_eq!(
        members(&initial_fault),
        members(&s["coins"]),
        "same member set"
    );

    // Sticky: later valid-looking acts never clear it.
    let m = mint(250, &p1.address, "");
    let p3 = pay("@alice", "@bob", 25, &open.address, &p1.address);
    let superset = [root, open, p1.clone(), p2.clone(), m, p3];
    let t = state(COIN, &superset);
    assert_fault_covers(&t["coins"], &[&p1.address, &p2.address]);
}

fn open_pair() -> Vec<Act> {
    vec![open("Alpha", "@a"), open("Beta", "@b")]
}

/// TEST-3800 on the one input that distinguishes `Sole::Top`: the term
/// evaluator's display of the `initial` carrier agrees with the shipped fold
/// member for member, in forward, reversed and duplicated delivery, and when
/// one of the openers lacks the payload.
#[test]
fn the_lattice_display_of_the_conflict_top_equals_the_fold() {
    let d = parse_dialect(&parse(OPENER_FORK).unwrap()).unwrap();
    let clause = d.state.as_ref().unwrap();
    let (name, rule) = clause.fields().next().unwrap();
    let f = factor(rule).expect("initial factors");
    let pair = open_pair();
    let missing = act(
        "(lang opener-fork (open @room :caused-by begin :thread \"t\" :from @c))",
        "@c",
    );
    let deliveries: Vec<Vec<Act>> = vec![
        pair.clone(),
        pair.iter().rev().cloned().collect(),
        [pair.clone(), pair.clone()].concat(),
        vec![pair[0].clone(), missing.clone()],
        vec![missing],
    ];
    for acts in deliveries {
        let folded = fold(clause, d.causal_protocol.as_ref(), &acts);
        let shipped = folded.iter().find(|(n, _)| n == name).unwrap().1.render();
        let term = Ctx::new(clause, &acts).display(&f, &[]).render();
        assert_eq!(term, shipped, "display of the term equals the fold");
    }
}
