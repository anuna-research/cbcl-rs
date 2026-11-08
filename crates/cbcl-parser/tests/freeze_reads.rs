//! SPEC-038 TEST-3802/3804: exact causal cuts and attributable late writes.
use cbcl_core::state::{fold, render_json, Act};
use cbcl_parser::{parse, parse_dialect, parse_message, state_exports};
use serde_json::{json, Value};

fn source(policy: &str) -> String {
    format!(
        "(define sealed (cbcl) @anuna
      (:roles (owner))
      (extend open (to) :from owner :to owner (tell to))
      (extend write (to value) :from owner :to owner (tell to :value value))
      (extend close (to) :from owner :to owner (tell to))
      (shape write (require :value string))
      (protocol (then begin open) (then open (repeat 2 write close)))
      (state (values (values write :value)) (freeze values close {policy})))"
    )
}

fn act(verb: &str, value: &str, pred: &str) -> Act {
    let fields = if verb == "write" {
        format!(" :value \"{value}\" :replaces ()")
    } else {
        String::new()
    };
    Act::from_message(
        parse_message(
            &parse(&format!(
        "(signed @owner (lang sealed ({verb} @owner{fields} :caused-by {pred} :thread \"t\" :from @owner)))"
            ))
            .unwrap(),
        )
        .unwrap(),
        "@owner",
    )
    .unwrap()
}

fn read(source: &str, acts: &[Act]) -> Value {
    let dialect = parse_dialect(&parse(source).unwrap()).unwrap();
    serde_json::from_str(&render_json(&fold(
        dialect.state.as_ref().unwrap(),
        dialect.causal_protocol.as_ref(),
        acts,
    )))
    .unwrap()
}

#[test]
fn freeze_keeps_its_causal_past_and_records_late_and_concurrent_writes() {
    let src = source("");
    state_exports::parse_and_install_dialect(&parse(&src).unwrap()).unwrap();
    let open = act("open", "", "begin");
    let before = act("write", "before", &open.address);
    let close = act("close", "", &before.address);
    let late = act("write", "late", &close.address);
    let concurrent = act("write", "concurrent", &open.address);
    assert_eq!(
        read(&src, &[open.clone(), before.clone()])["values"],
        json!(["before"])
    );
    let mut acts = vec![
        open,
        before,
        close.clone(),
        late.clone(),
        concurrent.clone(),
    ];
    let frozen = read(&src, &acts);
    assert_eq!(frozen["values"]["frozen"], close.address);
    assert_eq!(frozen["values"]["value"], json!(["before"]));
    let mut excluded = vec![late.address, concurrent.address];
    excluded.sort();
    assert_eq!(frozen["values"]["superseded"], json!(excluded));
    acts.reverse();
    acts.extend(acts.clone());
    assert_eq!(read(&src, &acts), frozen);
}

#[test]
fn fault_policy_names_the_freezer_and_late_writer() {
    let src = source("fault");
    state_exports::parse_and_install_dialect(&parse(&src).unwrap()).unwrap();
    let open = act("open", "", "begin");
    let before = act("write", "before", &open.address);
    let close = act("close", "", &before.address);
    let late = act("write", "late", &close.address);
    let mut evidence = vec![close.address.clone(), late.address.clone()];
    evidence.sort();
    let after = read(&src, &[open, before, close, late]);
    assert_eq!(after["values"]["status"], "fault");
    assert_eq!(after["values"]["evidence"], json!(evidence));
}

#[test]
fn installation_rejects_invalid_freeze_declarations() {
    for src in [
        source("unknown"),
        source("").replace("freeze values", "freeze missing"),
        source("").replace("freeze values close", "freeze values absent"),
        source("").replace(
            "(extend close (to) :from owner :to owner",
            "(extend close (to)",
        ),
        source("").replace(
            "(freeze values close )",
            "(freeze values close) (freeze values close fault)",
        ),
    ] {
        assert!(
            state_exports::parse_and_install_dialect(&parse(&src).unwrap()).is_err(),
            "{src}"
        );
    }
}

#[test]
fn thresholds_cannot_depend_on_a_revisable_supersede_freeze() {
    let add = |src: String, policy: &str| {
        src.replace(
            &format!("(freeze values close {policy})"),
            &format!(
                "(freeze values close {policy}) (arrivals (count write))
          (threshold quorum arrivals (count 1)) (freeze arrivals close {policy})"
            ),
        )
    };
    let unsafe_source = add(source("supersede"), "supersede");
    let error =
        state_exports::parse_and_install_dialect(&parse(&unsafe_source).unwrap()).unwrap_err();
    assert!(error.contains("unfrozen arrival field"), "{error}");
    let safe_source = add(source("fault"), "fault");
    state_exports::parse_and_install_dialect(&parse(&safe_source).unwrap()).unwrap();
    let open = act("open", "", "begin");
    let before = act("write", "before", &open.address);
    let close = act("close", "", &before.address);
    let closed = vec![open.clone(), before.clone(), close.clone()];
    assert_eq!(read(&safe_source, &closed)["quorum"]["status"], "reached");
    let late = act("write", "late", &close.address);
    assert_eq!(
        read(&safe_source, &[open, before, close, late])["quorum"]["status"],
        "fault"
    );
}

#[test]
fn repeated_causal_freezes_keep_the_first_cut_but_concurrent_freezes_fault() {
    let src = source("");
    let open = act("open", "", "begin");
    let first = act("write", "before", &open.address);
    let close = act("close", "", &first.address);
    let later = act("write", "later", &close.address);
    let second_close = act("close", "", &later.address);
    let after = read(
        &src,
        &[
            open.clone(),
            first.clone(),
            close.clone(),
            later,
            second_close,
        ],
    );
    assert_eq!(after["values"]["frozen"], close.address);
    assert_eq!(after["values"]["value"], json!(["before"]));
    let parallel = act("write", "parallel", &open.address);
    let parallel_close = act("close", "", &parallel.address);
    let after = read(
        &src,
        &[open, first, close.clone(), parallel, parallel_close.clone()],
    );
    let mut evidence = vec![close.address, parallel_close.address];
    evidence.sort();
    assert_eq!(after["values"]["status"], "fault");
    assert_eq!(after["values"]["evidence"], json!(evidence));
}

#[test]
fn derived_fields_read_frozen_source_values_and_can_freeze_their_own_result() {
    let src = source("")
        .replace("(require :value string)", "(require :value nonnegative)")
        .replace(
            "(values (values write :value))",
            "(values (events write :value)) (total (sum values))",
        )
        .replace(
            "(freeze values close )",
            "(freeze values close) (freeze total close)",
        );
    state_exports::parse_and_install_dialect(&parse(&src).unwrap()).unwrap();
    let open = act("open", "", "begin");
    let numeric = |n, pred: &str| {
        Act::from_message(
            parse_message(
                &parse(&format!(
        "(lang sealed (write @room :value {n} :caused-by {pred} :thread \"t\" :from @owner))"
    ))
                .unwrap(),
            )
            .unwrap(),
            "@owner",
        )
        .unwrap()
    };
    let before = numeric(3, &open.address);
    let close = act("close", "", &before.address);
    let late = numeric(9, &close.address);
    let after = read(&src, &[open, before, close.clone(), late]);
    assert_eq!(after["total"]["value"], 3);
    assert_eq!(after["total"]["frozen"], close.address);
}

#[test]
fn freeze_cannot_hide_a_later_initializer_conflict() {
    let src = source("").replace(
        "(extend open (to) :from owner :to owner (tell to))",
        "(extend open (to title) :from owner :to owner (tell to :title title)) (shape open (require :title string))")
        .replace("(values (values write :value))", "(title (initial open :title)) (freeze title close) (values (values write :value))");
    state_exports::parse_and_install_dialect(&parse(&src).unwrap()).unwrap();
    let make_open = |title: &str| {
        Act::from_message(
            parse_message(
                &parse(&format!(
        "(lang sealed (open @room :title \"{title}\" :caused-by begin :thread \"t\" :from @owner))"
    ))
                .unwrap(),
            )
            .unwrap(),
            "@owner",
        )
        .unwrap()
    };
    let a = make_open("first");
    let b = make_open("second");
    let write = act("write", "before", &a.address);
    let close = act("close", "", &write.address);
    assert_eq!(
        read(&src, &[a.clone(), write.clone(), close.clone()])["title"]["value"],
        "first"
    );
    let after = read(&src, &[a.clone(), write, close, b.clone()]);
    let mut evidence = vec![a.address, b.address];
    evidence.sort();
    assert_eq!(after["title"]["status"], "fault");
    assert_eq!(after["title"]["evidence"], json!(evidence));
}

#[test]
fn freezing_and_late_writes_use_normal_role_aware_admission() {
    use cbcl_core::store::ThreadId;
    use state_exports::Admission;
    let src = source("");
    let d = parse_dialect(&parse(&src).unwrap()).unwrap();
    let root = Act::from_message(parse_message(&parse(
        "(with-roles ((owner @owner)) (signed @owner (hello () :thread \"t\" :caused-by begin)))"
    ).unwrap()).unwrap(), "@owner").unwrap();
    let open = act("open", "", &root.address);
    let before = act("write", "before", &open.address);
    let close = act("close", "", &before.address);
    let late = act("write", "late", &close.address);
    let mut accepted = Vec::new();
    for next in [root, open, before, close, late] {
        let verdict = state_exports::admit(&d, &ThreadId("t".into()), &accepted, &next);
        assert!(
            matches!(verdict, Admission::Accepted),
            "{}: {verdict:?}",
            next.verb
        );
        accepted.push(next);
    }
    assert_eq!(read(&src, &accepted)["values"]["value"], json!(["before"]));
    let pred = &accepted.iter().find(|a| a.verb == "write").unwrap().address;
    let intruder = Act::from_message(parse_message(&parse(&format!(
        "(signed @intruder (lang sealed (close @owner :caused-by {pred} :thread \"t\" :from @intruder)))"
    )).unwrap()).unwrap(), "@intruder").unwrap();
    assert!(matches!(
        state_exports::admit(&d, &ThreadId("t".into()), &accepted, &intruder),
        Admission::Rejected(_)
    ));
}

#[test]
fn the_freezing_act_itself_is_in_the_exact_cut() {
    let src = source("").replace(
        "(freeze values close )",
        "(freeze values close) (closed (exists close)) (freeze closed close)",
    );
    state_exports::parse_and_install_dialect(&parse(&src).unwrap()).unwrap();
    let open = act("open", "", "begin");
    let write = act("write", "before", &open.address);
    let close = act("close", "", &write.address);
    let after = read(&src, &[open, write, close]);
    assert_eq!(after["closed"]["value"], true);
}

#[test]
fn schema_marks_snapshots_and_describes_the_freeze_transition() {
    let src = source("fault");
    let d = parse_dialect(&parse(&src).unwrap()).unwrap();
    let schema: Value = serde_json::from_str(&cbcl_core::state::render_schema(
        &cbcl_core::state::state_schema(d.state.as_ref().unwrap(), &d.shapes),
    ))
    .unwrap();
    assert_eq!(schema["values"]["observation"], "snapshot");
    assert_eq!(
        schema["values"]["freeze"],
        serde_json::json!({"verb":"close", "policy":"fault"})
    );
    assert!(read(&src, &[])["values"].get("frozen").is_none());
}

#[test]
fn additional_concurrent_freezer_preserves_the_late_writer_witness() {
    let src = source("fault");
    let open = act("open", "", "begin");
    let first = act("close", "", &open.address);
    let late = act("write", "late", &first.address);
    let second = act("close", "", &late.address);
    // A distinct concurrent root: same verb, different immutable predecessor.
    let concurrent = act("close", "", "begin");
    let initial = vec![open.clone(), first.clone(), late.clone(), second.clone()];
    let before = read(&src, &initial);
    let mut extended = initial;
    extended.push(concurrent.clone());
    let after = read(&src, &extended);
    assert_eq!(after["values"]["status"], "fault");
    for witness in before["values"]["evidence"].as_array().unwrap() {
        assert!(
            after["values"]["evidence"]
                .as_array()
                .unwrap()
                .contains(witness),
            "lost {witness}: {after}"
        );
    }
    assert!(after["values"]["evidence"]
        .as_array()
        .unwrap()
        .contains(&json!(concurrent.address)));
}

#[test]
fn initializer_conflict_preserves_an_existing_freeze_fault_witness() {
    let src = source("fault")
        .replace("(extend open (to) :from owner :to owner (tell to))",
            "(extend open (to title) :from owner :to owner (tell to :title title)) (shape open (require :title string))")
        .replace("(values (values write :value))", "(values (initial open :title))");
    state_exports::parse_and_install_dialect(&parse(&src).unwrap()).unwrap();
    let make_open = |title: &str, pred: &str| {
        Act::from_message(parse_message(&parse(&format!(
            "(signed @owner (lang sealed (open @owner :title {title:?} :caused-by {pred} :thread \"t\" :from @owner)))"
        )).unwrap()).unwrap(), "@owner").unwrap()
    };
    let open = make_open("first", "begin");
    let close = act("close", "", &open.address);
    let other = make_open("second", &close.address);
    let after = read(&src, &[open.clone(), close.clone(), other.clone()]);
    for address in [open.address, close.address, other.address] {
        assert!(
            after["values"]["evidence"]
                .as_array()
                .unwrap()
                .contains(&json!(address)),
            "lost {address}: {after}"
        );
    }
}

#[test]
fn domain_fault_cannot_erase_the_freeze_witness_of_an_admitted_contributor() {
    let src = source("fault")
        .replace("(extend open (to) :from owner :to owner (tell to))",
            "(extend open (to options) :from owner :to owner (tell to :options options)) (shape open (require :options list))")
        .replace("(values (values write :value))",
            "(options (initial open :options)) (domain write :value options) (values (values write :value))");
    state_exports::parse_and_install_dialect(&parse(&src).unwrap()).unwrap();
    let make_open = |option: &str| {
        Act::from_message(parse_message(&parse(&format!(
            "(lang sealed (open @owner :options ({option:?}) :caused-by begin :thread \"t\" :from @owner))"
        )).unwrap()).unwrap(), "@owner").unwrap()
    };
    let open = make_open("x");
    let close = act("close", "", &open.address);
    let late = act("write", "x", &close.address);
    let before = vec![open.clone(), close, late];
    let witness = read(&src, &before)["values"]["evidence"]
        .as_array()
        .unwrap()
        .clone();
    let mut after = before;
    after.push(make_open("y"));
    let value = read(&src, &after);
    for address in witness {
        assert!(
            value["values"]["evidence"]
                .as_array()
                .unwrap()
                .contains(&address),
            "lost {address}: {value}"
        );
    }
}

#[test]
fn fault_evidence_persists_across_all_closed_subhistories_of_a_forked_graph() {
    let src = source("fault")
        .replace("(extend open (to) :from owner :to owner (tell to))",
            "(extend open (to options) :from owner :to owner (tell to :options options)) (shape open (require :options list))")
        .replace("(values (values write :value))",
            "(options (initial open :options)) (domain write :value options) (values (values write :value))");
    state_exports::parse_and_install_dialect(&parse(&src).unwrap()).unwrap();
    let opener = |option: &str| {
        Act::from_message(parse_message(&parse(&format!(
        "(lang sealed (open @owner :options ({option:?}) :caused-by begin :thread \"t\" :from @owner))"
    )).unwrap()).unwrap(), "@owner").unwrap()
    };
    let a = opener("x");
    let b = opener("y");
    let x = act("write", "x", &a.address);
    let y = act("write", "y", &b.address);
    let f = act("close", "", &x.address);
    let g = act("close", "", &y.address);
    let late_x = act("write", "x", &f.address);
    let late_y = act("write", "y", &g.address);
    let graph = [a, b, x, y, f, g, late_x, late_y];
    let mut histories = Vec::new();
    for mask in 0usize..(1 << graph.len()) {
        let acts: Vec<Act> = graph
            .iter()
            .enumerate()
            .filter(|(i, _)| mask & (1 << i) != 0)
            .map(|(_, a)| a.clone())
            .collect();
        if acts.iter().all(|a| {
            a.predecessors
                .iter()
                .all(|p| acts.iter().any(|parent| parent.address == *p))
        }) {
            let observed = read(&src, &acts);
            histories.push((mask, observed));
        }
    }
    for (left, before) in &histories {
        for (right, after) in &histories {
            if left & right != *left {
                continue;
            }
            if let Some(witness) = before["values"]["evidence"].as_array() {
                assert_eq!(after["values"]["status"], "fault");
                let evidence = after["values"]["evidence"].as_array().unwrap();
                assert!(
                    witness.iter().all(|a| evidence.contains(a)),
                    "witness shrank: {left:08b} -> {right:08b}: {before} -> {after}"
                );
            }
        }
    }
}

#[test]
fn an_earlier_derived_freeze_cannot_hide_a_later_source_fault() {
    let src = source("fault")
        .replace("(require :value string)", "(require :value nonnegative)")
        .replace(
            "(extend close (to)",
            "(extend finish (to) :from owner :to owner (tell to)) (extend close (to)",
        )
        .replace("(repeat 2 write close)", "(repeat 2 write close finish)")
        .replace(
            "(values (values write :value))",
            "(values (events write :value)) (total (sum values))",
        )
        .replace(
            "(freeze values close fault)",
            "(freeze values finish fault) (freeze total close supersede)",
        );
    state_exports::parse_and_install_dialect(&parse(&src).unwrap()).unwrap();
    let numeric = |n, pred: &str| {
        Act::from_message(
            parse_message(
                &parse(&format!(
        "(lang sealed (write @owner :value {n} :caused-by {pred} :thread \"t\" :from @owner))"
    ))
                .unwrap(),
            )
            .unwrap(),
            "@owner",
        )
        .unwrap()
    };
    let open = act("open", "", "begin");
    let before = numeric(3, &open.address);
    let close = act("close", "", &before.address);
    let finish = act("finish", "", &close.address);
    let history = vec![open, before, close, finish.clone()];
    assert_eq!(read(&src, &history)["total"]["value"], 3);
    let mut extended = history;
    extended.push(numeric(9, &finish.address));
    let after = read(&src, &extended);
    assert_eq!(after["total"]["status"], "fault");
    assert_eq!(after["total"]["evidence"], after["values"]["evidence"]);
}

/// SPEC-038 REQ-3803/3806/3808: data domains cannot hide raw progress
/// contributors from a fault freeze or its dependent threshold.
#[test]
fn progress_fault_freeze_retains_domain_excluded_ticks() {
    let src = r#"(define raw-progress (cbcl) @author
      (:roles (owner))
      (extend open (to options) :from owner :to owner (tell to :options options))
      (extend tick (to target) :from owner :to owner (tell to :target target))
      (extend close (to) :from owner :to owner (tell to))
      (shape open (require :options list))
      (shape tick (require :target string))
      (protocol (then begin open) (then open (repeat 2 tick close)))
      (state (allowed (initial open :options))
        (domain tick :target allowed)
        (stage (progress tick)) (arrivals (count tick))
        (freeze stage close fault)
        (threshold first-stage stage (progress 1))))"#;
    state_exports::parse_and_install_dialect(&parse(src).unwrap()).unwrap();
    let make = |verb: &str, fields: &str, predecessor: &str| {
        Act::from_message(
            parse_message(&parse(&format!(
                "(signed @owner (lang raw-progress ({verb} @owner{fields} :from @owner :thread \"t\" :caused-by {predecessor})))"
            )).unwrap()).unwrap(), "@owner"
        ).unwrap()
    };
    let open = make("open", " :options (\"included\")", "begin");
    let tick = make("tick", " :target \"included\"", &open.address);
    let close = make("close", "", &tick.address);
    let late = make("tick", " :target \"excluded\"", &close.address);
    let before = read(src, &[open.clone(), tick.clone(), close.clone()]);
    assert_eq!(before["stage"]["value"], 1);
    assert_eq!(before["first-stage"]["status"], "reached");
    let mut history = vec![open, tick, close.clone(), late.clone()];
    let after = read(src, &history);
    assert_eq!(
        after["arrivals"], 1,
        "the data count still honors its domain"
    );
    assert_eq!(after["stage"]["status"], "fault");
    assert_eq!(after["first-stage"]["status"], "fault");
    let evidence = after["stage"]["evidence"].as_array().unwrap();
    assert!(evidence.contains(&json!(close.address)));
    assert!(evidence.contains(&json!(late.address)));
    history.reverse();
    history.extend(history.clone());
    assert_eq!(read(src, &history), after);

    // Supersede also retains the raw tick in its excluded-write metadata.
    // Its source cannot have a threshold, so remove that declaration here.
    let supersede = src
        .replace(
            "(freeze stage close fault)",
            "(freeze stage close supersede)",
        )
        .replace("(threshold first-stage stage (progress 1))", "");
    state_exports::parse_and_install_dialect(&parse(&supersede).unwrap()).unwrap();
    let sealed = read(&supersede, &history);
    assert_eq!(sealed["stage"]["value"], 1);
    assert_eq!(sealed["stage"]["superseded"], json!([late.address]));
    assert_eq!(sealed["arrivals"], 1);
}

/// Resource operation domains reject at installation, before freeze evaluation.
#[test]
fn resource_domains_cannot_hide_freeze_contributors() {
    let src = r#"(define raw-resource (cbcl) @author
      (:roles (owner))
      (extend open (to allocations options) :from owner :to owner (tell to :allocations allocations :options options))
      (extend mint (to amount target) :from owner :to owner (tell to :amount amount :target target))
      (extend burn (to amount) :from owner :to owner (tell to :amount amount))
      (extend pay (to recipient amount) :from owner :to owner (tell to :recipient recipient :amount amount))
      (extend close (to) :from owner :to owner (tell to))
      (shape open (require :allocations list) (require :options list))
      (shape mint (require :amount number) (require :target string))
      (shape burn (require :amount number))
      (shape pay (require :recipient symbol) (require :amount number))
      (protocol (then begin open) (then open (repeat 2 mint close)) (then open burn) (then open pay))
      (state (allowed (initial open :options)) (domain mint :target allowed)
        (coins (bounded-counter (floor 0) (initial-rights open :allocations)
          (issuers owner) (increment mint :amount) (decrement burn :amount) (transfer pay :recipient :amount)))
        (arrivals (count mint)) (freeze coins close fault)))"#;
    let error = state_exports::parse_and_install_dialect(&parse(src).unwrap()).unwrap_err();
    assert!(
        error.contains("domain may not hide resource acts of 'mint'"),
        "{error}"
    );
}
