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
