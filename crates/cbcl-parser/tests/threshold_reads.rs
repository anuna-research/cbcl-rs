//! SPEC-038 threshold reads (REQ-3802, CON-3801).
//!
//! TEST-3801: a dialect declaring thresholds over `count`, `set-union`,
//! nonnegative numeric `events` and `progress`; any permutation and duplication of a
//! delivery reaches the same element, across the growth of the accepted set
//! an element is reached at most once (pending… then reached, never pending
//! again) on non-conflicting growth. Conflicts produce separate terminal faults.
//!
//! TEST-3803: installation rejects a threshold set whose elements are not
//! pairwise incompatible, an element not admitted by the field's carrier, an
//! undeclared field and a threshold declared before its field; and the
//! pairwise check runs in `O(k²)` comparisons.
//!
//! The kernel is a function of the accepted set, so the tests feed acts to
//! `fold` directly, restricted to causally closed prefixes as admission would
//! produce them (SPEC-038 REQ-3800).
use cbcl_core::lattice::{pairwise, Element};
use cbcl_core::state::{fold, render_json, render_schema, state_schema, Act, Value as V};
use cbcl_parser::state_exports::{self, parse_and_install_dialect, Admission};
use cbcl_parser::{parse, parse_dialect, parse_message};
use proptest::prelude::*;
use serde_json::{json, Value};
use std::collections::BTreeSet;

const DEMO: &str = "(define threshold-demo (cbcl) @anuna \
  (extend open (to) (tell to)) \
  (extend tick (to) (tell to)) \
  (extend approve (to) (tell to)) \
  (extend tag (to label) (tell to :label label)) \
  (extend mint (to amount) (tell to :amount amount)) \
  (extend burn (to amount) (tell to :amount amount)) \
  (shape tag (require :label string)) \
  (shape mint (require :amount nonnegative)) \
  (shape burn (require :amount number)) \
  (protocol (then begin open) (then open (repeat 3 tick)) (then open approve) (then open tag) (then open mint) (then open burn)) \
  (state \
    (approvals (count approve)) \
    (threshold quorum approvals (count 2)) \
    (tags (set-union tag :label)) \
    (threshold tagged tags (member \"x\")) \
    (balance (counter mint burn :amount)) \
    (credits (events mint :amount)) \
    (threshold funded credits (sum 10)) \
    (stage (progress tick)) \
    (threshold done stage (progress 2))))";

const THRESHOLDS: [&str; 4] = ["quorum", "tagged", "funded", "done"];

fn act(canonical: &str, signer: &str) -> Act {
    Act::from_message(parse_message(&parse(canonical).unwrap()).unwrap(), signer).unwrap()
}

fn demo(verb: &str, params: &str, pred: &str, signer: &str) -> Act {
    act(
        &format!(
            "(lang threshold-demo ({verb} @room{params} :caused-by {pred} :thread \"t\" :from {signer}))"
        ),
        signer,
    )
}

fn open() -> Act {
    demo("open", "", "begin", "@opener")
}

fn state_of(source: &str, acts: &[Act]) -> Value {
    let d = parse_dialect(&parse(source).unwrap()).unwrap();
    serde_json::from_str(&render_json(&fold(
        d.state.as_ref().unwrap(),
        d.causal_protocol.as_ref(),
        acts,
    )))
    .unwrap()
}

fn install(source: &str) -> Result<(), String> {
    parse_and_install_dialect(&parse(source).unwrap()).map(|_| ())
}

/// The largest causally closed subset of `acts`: what admission (R.1)
/// would have accepted from this delivery.
fn closed(acts: &[Act]) -> Vec<Act> {
    let mut present: BTreeSet<String> = BTreeSet::new();
    loop {
        let next: BTreeSet<String> = acts
            .iter()
            .filter(|a| {
                a.predecessors
                    .iter()
                    .all(|p| p == "begin" || present.contains(p))
            })
            .map(|a| a.address.clone())
            .collect();
        if next == present {
            break;
        }
        present = next;
    }
    acts.iter()
        .filter(|a| present.contains(&a.address))
        .cloned()
        .collect()
}

// ---------------------------------------------------------------------------
// Rendering shape and clause order
// ---------------------------------------------------------------------------

#[test]
fn a_threshold_is_pending_then_reached_with_its_element() {
    let o = open();
    let s = state_of(DEMO, std::slice::from_ref(&o));
    for t in THRESHOLDS {
        assert_eq!(s[t], json!({"status": "pending"}), "{t}");
    }
    let a1 = demo("approve", "", &o.address, "@a");
    let a2 = demo("approve", "", &o.address, "@b");
    let s = state_of(DEMO, &[o.clone(), a1.clone()]);
    assert_eq!(s["approvals"], 1);
    assert_eq!(s["quorum"], json!({"status": "pending"}));
    let s = state_of(DEMO, &[o.clone(), a1, a2]);
    assert_eq!(s["approvals"], 2);
    assert_eq!(
        s["quorum"],
        json!({"status": "reached", "element": {"count": 2}})
    );

    let tx = demo("tag", " :label \"x\"", &o.address, "@a");
    let ty = demo("tag", " :label \"y\"", &o.address, "@a");
    let s = state_of(DEMO, &[o.clone(), ty.clone()]);
    assert_eq!(s["tagged"], json!({"status": "pending"}));
    let s = state_of(DEMO, &[o.clone(), ty, tx]);
    assert_eq!(
        s["tagged"],
        json!({"status": "reached", "element": {"member": "x"}})
    );

    let m1 = demo("mint", " :amount 6", &o.address, "@m1");
    let m2 = demo("mint", " :amount 6", &o.address, "@m2");
    let b = demo("burn", " :amount 5", &o.address, "@b");
    let s = state_of(DEMO, &[o.clone(), m1.clone(), b.clone()]);
    assert_eq!(s["balance"], 1);
    assert_eq!(s["funded"], json!({"status": "pending"}));
    // Gross credits are explicitly named; the signed balance stays a snapshot.
    let s = state_of(DEMO, &[o.clone(), m1, m2, b]);
    assert_eq!(s["balance"], 7);
    assert_eq!(
        s["funded"],
        json!({"status": "reached", "element": {"sum": 10}})
    );

    let t1 = demo("tick", "", &o.address, "@a");
    let t2 = demo("tick", "", &t1.address, "@b");
    let s = state_of(DEMO, &[o.clone(), t1.clone()]);
    assert_eq!(s["stage"], 1);
    assert_eq!(s["done"], json!({"status": "pending"}));
    let s = state_of(DEMO, &[o, t1, t2]);
    assert_eq!(s["stage"], 2);
    assert_eq!(
        s["done"],
        json!({"status": "reached", "element": {"progress": 2}})
    );
}

// REQ-3802: shape validation must constrain the same numeric value the fold reads.
#[test]
fn duplicate_amount_cannot_hide_a_negative_state_contribution() {
    let d = parse_dialect(&parse(DEMO).unwrap()).unwrap();
    let o = open();
    let candidate = demo("mint", " :amount 10 :amount -1", &o.address, "@a");
    assert_eq!(candidate.fields["amount"].to_string(), "-1");
    let positive = demo("mint", " :amount 10", &o.address, "@b");
    assert!(matches!(
        state_exports::admit(&d, &cbcl_core::store::ThreadId("t".into()), &[o.clone()], &positive),
        Admission::Accepted
    ));
    let before = state_of(DEMO, &[o.clone(), positive.clone()]);
    let after = state_of(DEMO, &[o.clone(), positive.clone(), candidate.clone()]);
    assert_eq!(before["funded"]["status"], "reached");
    assert_eq!(after["funded"]["status"], "pending");
    let verdict = state_exports::admit(
        &d, &cbcl_core::store::ThreadId("t".into()), &[o.clone(), positive], &candidate,
    );
    assert!(matches!(verdict, Admission::Rejected(_)), "ambiguous amount admitted: {verdict:?}");
    for params in [" :amount 10 :amount 10", " :amount 0 :amount 1", " :amount -1 :amount 10"] {
        let duplicate = demo("mint", params, &o.address, "@a");
        let error = cbcl_core::r7::verify_state_shape(&d, &duplicate.message).unwrap_err();
        assert!(error.to_string().contains("duplicate state keyword"));
    }
}

/// REQ-3802 / ADR-3805: nonnegative amounts are recognized before admission;
/// signed net balances retain their snapshot meaning.
#[test]
fn negative_credits_are_rejected_and_signed_balances_remain_snapshots() {
    assert_eq!(install(DEMO), Ok(()));
    let o = open();
    let positive = demo("mint", " :amount 10", &o.address, "@a");
    let negative = demo("mint", " :amount -1", &o.address, "@b");
    let before = state_of(DEMO, &[o.clone(), positive.clone()]);
    assert_eq!(before["funded"]["status"], "reached");
    let d = parse_dialect(&parse(DEMO).unwrap()).unwrap();
    assert!(matches!(
        state_exports::admit(
            &d,
            &cbcl_core::store::ThreadId("t".into()),
            &[o.clone(), positive.clone()],
            &negative
        ),
        Admission::Rejected(_)
    ));
    let signed = DEMO
        .replace("(require :amount nonnegative)", "(require :amount number)")
        .replace("(threshold funded credits (sum 10))", "");
    assert_eq!(install(&signed), Ok(()));
    assert_eq!(
        state_of(&signed, &[o.clone(), positive.clone()])["balance"],
        10
    );
    assert_eq!(state_of(&signed, &[o, positive, negative])["balance"], 9);
    assert!(install(&DEMO.replace("funded credits", "funded balance"))
        .unwrap_err()
        .contains("snapshot"));
    assert!(install(&DEMO.replace("nonnegative", "number"))
        .unwrap_err()
        .contains("nonnegative"));
}

#[test]
fn a_threshold_renders_as_a_field_named_name_in_clause_order() {
    let d = parse_dialect(&parse(DEMO).unwrap()).unwrap();
    let folded = fold(d.state.as_ref().unwrap(), d.causal_protocol.as_ref(), &[]);
    let names: Vec<&str> = folded.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(
        names,
        [
            "approvals",
            "quorum",
            "tags",
            "tagged",
            "balance",
            "credits",
            "funded",
            "stage",
            "done"
        ]
    );
    // Existing fields render exactly as before: a threshold adds a member
    // and changes nothing else (REQ-3807).
    let text = render_json(&folded);
    assert!(text.starts_with("{\"approvals\":0,\"quorum\":{\"status\":\"pending\"},\"tags\":[]"));
}

#[test]
fn the_schema_types_a_threshold_by_its_field_and_elements() {
    let d = parse_dialect(&parse(DEMO).unwrap()).unwrap();
    let schema: Value = serde_json::from_str(&render_schema(&state_schema(
        d.state.as_ref().unwrap(),
        &d.shapes,
    )))
    .unwrap();
    assert_eq!(
        schema["approvals"],
        json!({"type": "int", "observation": "snapshot"})
    );
    assert_eq!(
        schema["quorum"],
        json!({"type": "threshold", "field": "approvals", "elements": [{"count": 2}]})
    );
    assert_eq!(
        schema["tagged"],
        json!({"type": "threshold", "field": "tags", "elements": [{"member": "x"}]})
    );
    assert_eq!(
        schema["funded"],
        json!({"type": "threshold", "field": "credits", "elements": [{"sum": 10}]})
    );
    assert_eq!(
        schema["done"],
        json!({"type": "threshold", "field": "stage", "elements": [{"progress": 2}]})
    );
    let keys: Vec<&String> = schema.as_object().unwrap().keys().collect();
    assert_eq!(keys.len(), 9);
}

/// Initial conflicts are automatic faults; a bare `#t` reads the bool carrier.
#[test]
fn fault_and_scalar_elements_read_the_top_and_the_bool_carrier() {
    const FORK: &str = "(define opener-fork (cbcl) @anuna \
      (extend open (to title) (tell to :title title)) \
      (extend close (to) (tell to)) \
      (shape open (require :title string)) \
      (protocol (then begin open) (then open close)) \
      (state (title (initial open :title)) \
             (closed (exists close)) (threshold shut closed #t)))";
    let a = act(
        "(lang opener-fork (open @room :title \"Alpha\" :caused-by begin :thread \"t\" :from @a))",
        "@a",
    );
    let b = act(
        "(lang opener-fork (open @room :title \"Beta\" :caused-by begin :thread \"t\" :from @b))",
        "@b",
    );
    let c = act(
        &format!(
            "(lang opener-fork (close @room :caused-by {} :thread \"t\" :from @a))",
            a.address
        ),
        "@a",
    );
    let s = state_of(FORK, std::slice::from_ref(&a));
    assert_eq!(s["title"], "Alpha");
    assert_eq!(s["shut"], json!({"status": "pending"}));
    let s = state_of(FORK, &[a.clone(), b.clone(), c.clone()]);
    assert_eq!(s["title"]["status"], "fault");
    assert_eq!(s["shut"], json!({"status": "reached", "element": true}));
    let s = state_of(FORK, &[b, a, c]);
    assert_eq!(s["title"]["status"], "fault");
}

#[test]
fn initializer_conflict_faults_progress_and_its_reached_threshold() {
    let source = "(define closure-fork (cbcl) @anuna
      (extend open (to options) (tell to :options options))
      (extend tick (to choice) (tell to :choice choice))
      (shape open (require :options list)) (shape tick (require :choice string))
      (protocol (then begin open) (then open (repeat 3 tick)))
      (state (options (initial open :options)) (domain tick :choice options)
             (stage (progress tick)) (threshold done stage (progress 1))))";
    assert_eq!(install(source), Ok(()));
    let a = act("(lang closure-fork (open @room :options (\"yes\") :caused-by begin :thread \"t\" :from @a))", "@a");
    let b = act("(lang closure-fork (open @room :options (\"no\") :caused-by begin :thread \"t\" :from @b))", "@b");
    let tick = act(
        &format!(
            "(lang closure-fork (tick @room :choice \"yes\" :caused-by {} :thread \"t\" :from @a))",
            a.address
        ),
        "@a",
    );
    let before = state_of(source, &[a.clone(), tick.clone()]);
    assert_eq!(before["stage"], 1);
    assert_eq!(before["done"]["status"], "reached");
    let mut evidence = vec![a.address.clone(), b.address.clone()];
    evidence.sort();
    for acts in [
        vec![a.clone(), tick.clone(), b.clone()],
        vec![b, tick.clone(), a, tick],
    ] {
        let after = state_of(source, &acts);
        for field in ["stage", "done"] {
            assert_eq!(after[field]["status"], "fault", "{field}");
            assert_eq!(after[field]["evidence"], json!(evidence), "{field}");
        }
    }
}

// ---------------------------------------------------------------------------
// TEST-3801: threshold determinism
// ---------------------------------------------------------------------------

/// A delivery: the opener plus approvals, tags, mints, burns and a tick chain.
fn delivery(
    approvers: &[usize],
    tags: &[(usize, usize)],
    mints: &[(usize, i64)],
    burns: &[(usize, i64)],
    ticks: usize,
) -> Vec<Act> {
    let o = open();
    let who = ["@a", "@b", "@c", "@d"];
    let labels = ["\"x\"", "\"y\"", "\"z\""];
    let mut acts = vec![o.clone()];
    for i in approvers {
        acts.push(demo("approve", "", &o.address, who[*i]));
    }
    for (w, l) in tags {
        acts.push(demo(
            "tag",
            &format!(" :label {}", labels[*l]),
            &o.address,
            who[*w],
        ));
    }
    for (w, n) in mints {
        acts.push(demo("mint", &format!(" :amount {n}"), &o.address, who[*w]));
    }
    for (w, n) in burns {
        acts.push(demo("burn", &format!(" :amount {n}"), &o.address, who[*w]));
    }
    let mut pred = o.address.clone();
    for i in 0..ticks {
        let t = demo("tick", "", &pred, who[i % who.len()]);
        pred = t.address.clone();
        acts.push(t);
    }
    acts
}

fn delivery_strategy() -> impl Strategy<Value = Vec<Act>> {
    (
        proptest::collection::btree_set(0usize..4, 0..=4),
        proptest::collection::vec((0usize..4, 0usize..3), 0..=4),
        proptest::collection::vec((0usize..4, 1i64..=6), 0..=4),
        proptest::collection::vec((0usize..4, 1i64..=6), 0..=2),
        0usize..=3,
    )
        .prop_map(|(approvers, tags, mints, burns, ticks)| {
            let approvers: Vec<usize> = approvers.into_iter().collect();
            delivery(&approvers, &tags, &mints, &burns, ticks)
        })
}

/// A permutation of the delivery with some acts delivered again.
fn permuted(delivery: Vec<Act>) -> impl Strategy<Value = Vec<Act>> {
    let n = delivery.len();
    (
        Just(delivery).prop_shuffle(),
        proptest::collection::vec(0usize..n, 0..=n),
    )
        .prop_map(|(mut acts, dups)| {
            for i in dups {
                let a = acts[i].clone();
                acts.push(a);
            }
            acts
        })
}

fn thresholds(s: &Value) -> Vec<(&'static str, Value)> {
    THRESHOLDS.iter().map(|t| (*t, s[*t].clone())).collect()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// Every permutation and duplication of a delivery reaches the same
    /// element; across causally closed prefixes an element is reached at most
    /// once and never retracted; and no superset retracts it (REQ-3802).
    #[test]
    fn threshold_reads_are_deterministic_reached_once_and_never_retracted(
        (original, perm) in delivery_strategy().prop_flat_map(|d| (Just(d.clone()), permuted(d)))
    ) {
        let d = parse_dialect(&parse(DEMO).unwrap()).unwrap();
        let clause = d.state.as_ref().unwrap();
        let fold_json = |acts: &[Act]| -> Value {
            serde_json::from_str(&render_json(&fold(clause, d.causal_protocol.as_ref(), acts))).unwrap()
        };
        let want = thresholds(&fold_json(&original));
        prop_assert_eq!(thresholds(&fold_json(&perm)), want.clone(), "permutation and duplication");

        // Across the growth of the accepted set: pending… then reached with
        // one element, never pending or another element again.
        let mut seen: Vec<(&str, Option<Value>)> = THRESHOLDS.iter().map(|t| (*t, None)).collect();
        for end in 0..=perm.len() {
            let s = fold_json(&closed(&perm[..end]));
            for (t, reached) in seen.iter_mut() {
                let now = s[*t].clone();
                prop_assert!(now["status"] == "pending" || now["status"] == "reached", "{t}: {now}");
                match reached {
                    None => {
                        if now["status"] == "reached" {
                            *reached = Some(now);
                        }
                    }
                    Some(before) => prop_assert_eq!(&now, before, "{} retracted or re-reached", t),
                }
            }
        }
        let last = fold_json(&closed(&perm));
        for (t, reached) in &seen {
            prop_assert_eq!(&last[*t], &reached.clone().unwrap_or(json!({"status": "pending"})), "{}", t);
        }

        // Supersets: further valid acts never retract a reached element.
        let o = &original[0];
        let last_tick = original.iter().rfind(|a| a.verb == "tick").map(|a| a.address.clone()).unwrap_or(o.address.clone());
        let more = vec![
            demo("approve", "", &o.address, "@e"),
            demo("tag", " :label \"x\"", &o.address, "@e"),
            demo("mint", " :amount 100", &o.address, "@e"),
            demo("burn", " :amount 100", &o.address, "@e"),
            demo("tick", "", &last_tick, "@e"),
        ];
        let mut grown = original.clone();
        for extra in more {
            grown.push(extra);
            let s = fold_json(&grown);
            for (t, element) in &want {
                if element["status"] == "reached" {
                    prop_assert_eq!(&s[*t], element, "{} retracted on a superset", t);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// TEST-3803: install rejects compatible thresholds and mistyped elements
// ---------------------------------------------------------------------------

/// A coin dialect whose `coins` is a nonnegative numeric events stream
/// and whose `flag` is an `exists` (carrier `bool`).
fn coin(thresholds: &str) -> String {
    format!(
        "(define coin (cbcl) @anuna \
          (extend open (to) (tell to)) \
          (extend mint (to amount) (tell to :amount amount)) \
          (extend burn (to amount) (tell to :amount amount)) \
          (extend tag (to label) (tell to :label label)) \
          (extend close (to) (tell to)) \
          (shape mint (require :amount nonnegative)) \
          (shape burn (require :amount number)) \
          (shape tag (require :label string)) \
          (protocol (then begin open) (then open mint) (then open burn) (then open tag) (then open close)) \
          (state (coins (events mint :amount)) (balance (counter mint burn :amount)) (flag (exists close)) \
                 (labels (set-union tag :label)) (picked (values tag :label)) {thresholds}))"
    )
}

#[test]
fn install_rejects_a_compatible_pair_and_accepts_an_incompatible_one() {
    let e = install(&coin("(threshold t coins (sum 10) (sum 20))")).unwrap_err();
    assert!(
        e.contains("threshold t")
            && e.contains("(sum 10)")
            && e.contains("(sum 20)")
            && e.contains("compatible"),
        "{e}"
    );
    for declaration in [
        "(threshold t coins (sum 10) fault)",
        "(threshold t coins fault (sum 10))",
        "(threshold t flag #t fault)",
        "(threshold t coins fault)",
    ] {
        assert!(install(&coin(declaration))
            .unwrap_err()
            .contains("terminal outcome"));
    }
    assert_eq!(install(&coin("(threshold t coins (sum 10))")), Ok(()));
    let e = install(&coin("(threshold t coins (member 1) (sum 10))")).unwrap_err();
    assert!(e.contains("compatible"), "{e}");
}

#[test]
fn install_rejects_a_duplicate_element() {
    let e = install(&coin("(threshold t flag #t #t)")).unwrap_err();
    assert!(e.contains("threshold t") && e.contains("duplicate"), "{e}");
    let e = install(&coin("(threshold t coins fault fault)")).unwrap_err();
    assert!(e.contains("terminal outcome"), "{e}");
    let e = install(&coin("(threshold t labels (member \"a\") (member \"a\"))")).unwrap_err();
    assert!(e.contains("duplicate"), "{e}");
    // Two members are compatible: the set {a, b} lies above both.
    let e = install(&coin("(threshold t labels (member \"a\") (member \"b\"))")).unwrap_err();
    assert!(
        e.contains("(member \"a\")") && e.contains("(member \"b\")") && e.contains("compatible"),
        "{e}"
    );
}

#[test]
fn install_rejects_an_element_the_carrier_does_not_admit() {
    // `count n` against the `vals` carrier of set-union.
    let e = install(&coin("(threshold t labels (count 2))")).unwrap_err();
    assert!(e.contains("(count 2)") && e.contains("vals"), "{e}");
    // …and against the superseding carrier of `values`.
    let e = install(&coin("(threshold t picked (count 2))")).unwrap_err();
    assert!(e.contains("(count 2)"), "{e}");
    // `sum n` against bool; a bare scalar against amounts; progress against
    // a lift; `#f` is ⊥, not an element.
    assert!(install(&coin("(threshold t flag (sum 1))"))
        .unwrap_err()
        .contains("snapshot"));
    assert!(install(&coin("(threshold t coins #t)"))
        .unwrap_err()
        .contains("#t"));
    assert!(install(&coin("(threshold t coins (progress 1))"))
        .unwrap_err()
        .contains("(progress 1)"));
    assert!(install(&coin("(threshold t flag #f)")).is_err());
    // CON-3801 types against the carrier, not the writer's shape. A
    // scalar member is well typed even if this dialect never contributes it.
    assert_eq!(install(&coin("(threshold t labels (member 7))")), Ok(()));
}

#[test]
fn install_rejects_an_undeclared_field_a_threshold_before_its_field_and_a_clashing_name() {
    let e = install(&coin("(threshold t nothing (sum 1))")).unwrap_err();
    assert!(e.contains("threshold t") && e.contains("nothing"), "{e}");
    let src = coin("").replace(
        "(state (coins",
        "(state (threshold early coins (sum 1)) (coins",
    );
    let e = install(&src).unwrap_err();
    assert!(e.contains("early") && e.contains("coins"), "{e}");
    let e = install(&coin("(threshold coins coins (sum 1))")).unwrap_err();
    assert!(e.contains("coins"), "{e}");
    let e = install(&coin("(threshold t coins (sum 1)) (threshold t flag #t)")).unwrap_err();
    assert!(e.contains("duplicate") && e.contains("'t'"), "{e}");
}

#[test]
fn the_parser_rejects_malformed_threshold_entries() {
    assert!(install(&coin("(threshold t coins)")).is_err());
    assert!(install(&coin("(threshold Bad coins (sum 1))")).is_err());
    assert!(install(&coin("(threshold t coins (count))")).is_err());
    assert!(install(&coin("(threshold t coins (sum \"x\"))")).is_err());
    assert!(install(&coin("(threshold t coins (unknown 1))")).is_err());
    assert!(install(&coin("(threshold t coins notfault)")).is_err());
}

/// NFR-3800: the pairwise check is `O(k²)` comparisons. The shipped successful
/// threshold sources admit mutually compatible alternatives, so no dialect
/// can install `k = 64` incompatible elements before finite lattice support. The
/// bound is therefore asserted on the comparison count itself: the pairwise
/// walk over `k` elements that all compare incompatible makes exactly
/// `k(k-1)/2` comparisons and accepts.
#[test]
fn the_pairwise_check_makes_k_choose_2_comparisons() {
    let k = 64;
    let elements: Vec<Element> = (1..=k).map(|n| Element::Sum(n as i64)).collect();
    let mut comparisons = 0usize;
    let verdict = pairwise(&elements, |_, _| {
        comparisons += 1;
        None
    });
    assert_eq!(verdict, Ok(()));
    assert_eq!(comparisons, k * (k - 1) / 2);
    // On a chain the first compatible pair ends the walk.
    let mut comparisons = 0usize;
    let verdict = pairwise(&elements, |a, b| {
        comparisons += 1;
        cbcl_core::lattice::relation(a, b)
    });
    assert_eq!(verdict, Err((0, 1, "compatible")));
    assert_eq!(comparisons, 1);
    // And through the installer: a 64-element chain is rejected naming the
    // first pair.
    let chain: String = (1..=k).map(|n| format!(" (sum {n})")).collect();
    let e = install(&coin(&format!("(threshold t coins{chain})"))).unwrap_err();
    assert!(e.contains("(sum 1)") && e.contains("(sum 2)"), "{e}");
}

#[test]
fn elements_render_round_trip_the_wire_form() {
    let cases: Vec<(Element, &str, &str)> = vec![
        (Element::Count(2), "(count 2)", "{\"count\":2}"),
        (
            Element::Member(V::Str("x".into())),
            "(member \"x\")",
            "{\"member\":\"x\"}",
        ),
        (Element::Sum(10), "(sum 10)", "{\"sum\":10}"),
        (Element::Progress(3), "(progress 3)", "{\"progress\":3}"),
        (Element::Scalar(V::Bool(true)), "#t", "true"),
    ];
    for (e, wire, json) in cases {
        assert_eq!(e.wire(), wire);
        assert_eq!(e.render().render(), json);
    }
}
