//! Installed-dialect, native-certificate continuation across all kernel heads.
use crate::{certificate::SignedMessage, member::Client, test_support::*};
use cbcl_core::state::{self, Act};

#[test]
fn two_thousand_events_keep_selected_values_without_message_bodies() {
    use crate::summary::Summary;
    use cbcl_core::state::{Entry, Rule, StateClause};
    use std::collections::BTreeSet;
    let f = Fixture::new();
    let clause = StateClause {
        entries: vec![Entry::Field {
            name: "events".into(),
            rule: Rule::Events {
                verb: "write".into(),
                key: "value".into(),
            },
        }],
    };
    let mut summary = Summary::new(&clause, None).unwrap();
    let mut covered = BTreeSet::new();
    let mut history = Vec::new();
    let mut body_bytes = 0;
    let unused = "unused-payload-".repeat(320);
    for i in 0..2000 {
        let message = SignedMessage::sign(parse(&format!(
            "(lang {} (write @m0 :value {i} :unused \"{unused}\" :from @m0 :sender @m0 :thread \"target\" :caused-by begin))",
            f.context.target().name
        )), "@m0", &f.keys).unwrap();
        body_bytes += message.encode().len();
        let act = message.authenticate(&f.keys).unwrap();
        summary.apply(&act, |id| covered.contains(id)).unwrap();
        covered.insert(act.address.clone());
        history.push(act);
    }
    let bytes = summary.encode();
    let restored = Summary::decode(&bytes, &clause).unwrap();
    assert_eq!(restored.render(), state::fold(&clause, None, &history));
    assert!(!bytes.windows(15).any(|w| w == b"unused-payload-"));
    assert!(body_bytes > 10 * bytes.len());
    println!("events-projection messages=2000 signed_body_bytes={body_bytes} checkpoint_bytes={} reduction={:.2}", bytes.len(), body_bytes as f64 / bytes.len() as f64);
}

fn fixture() -> Fixture {
    let mut f = Fixture::with_target(installed(
        r#"(define all-head-checkpoint (cbcl) @anuna
      (:roles ((* member)))
      (extend open (to title allocations) :from member :to member (tell to :title title :allocations allocations))
      (extend write (to item value clock) :from member :to member (tell to :item item :value value :clock clock))
      (extend drop (to item) :from member :to member (tell to :item item))
      (extend pay (to recipient amount) :from member :to member (tell to :recipient recipient :amount amount))
      (extend burn (to value) :from member :to member (tell to :value value))
      (shape pay (require :recipient symbol) (require :amount integer))
      (shape burn (require :value integer))
      (shape open (require :title string) (require :allocations list))
      (shape write (require :item string) (require :value integer) (require :clock hlc) (require :unused string))
      (shape drop (require :item string))
      (protocol (then begin open) (then open (repeat 8 write)) (then open drop) (then open pay) (then open burn))
      (state
        (title (initial open :title))
        (present (exists write))
        (writes (count write))
        (position (progress write))
        (events (events write :value))
        (union (set-union write :value))
        (values (values write :value))
        (by-key (values-per-key write :item :value drop))
        (observed (observed-set write drop :item))
        (counter (counter write burn :value))
        (register (lww-register write :value :clock))
        (by-signer (lww-per-signer write :value :clock))
        (map (lww-map write :item :value :clock drop))
        (distribution (histogram map))
        (total (sum events))
        (resource (bounded-counter (floor 0) (initial-rights open :allocations)
          (issuers member) (increment write :value) (decrement burn :value) (transfer pay :recipient :amount)))))
    "#,
    ));
    f.target_open = SignedMessage::sign(parse(&format!(
        "(lang {} (open (@m0 @m1 @m2 @m3) :title \"Drawing\" :allocations ((@m0 10) (@m1 0) (@m2 0) (@m3 0)) :from @m0 :sender @m0 :thread \"target\" :caused-by \"{}\"))",
        f.context.target().name, f.context.target_root().id().unwrap()
    )), "@m0", &f.keys).unwrap();
    f
}

#[test]
fn all_sixteen_installed_heads_resume_native_certificates_at_every_cut() {
    let f = fixture();
    let mut messages = Vec::new();
    let mut previous = f.target_open.id().unwrap();
    for i in 1..=8 {
        let message = SignedMessage::sign(parse(&format!(
            "(lang {} (write (@m0 @m1 @m2 @m3) :item \"shape\" :value {} :clock \"hlc-{:016x}-00000000\" :replaces ({}) :unused \"discard-me\" :escrow-prev {} :escrow-deps () :from @m0 :sender @m0 :thread \"target\" :caused-by \"{}\"))",
            f.context.target().name, i, i, messages.last().map(|m: &SignedMessage|m.authenticate(&f.keys).unwrap().address).unwrap_or_default(), previous, previous
        )), "@m0", &f.keys).unwrap();
        previous = message.id().unwrap();
        messages.push(message);
    }
    let clause = f.context.target().state.as_ref().unwrap();
    assert_eq!(clause.fields().count(), 16);
    let history: Vec<Act> = vec![
        f.context.target_root().authenticate(&f.keys).unwrap(),
        f.target_open.authenticate(&f.keys).unwrap(),
    ];
    for cut in 0..=messages.len() {
        let mut members = f.members(&messages[..cut]);
        let certificate = f.certificate(&members);
        let mut client = Client::from_certificate(&f.context, &certificate, &f.keys).unwrap();
        let mut prefix = history.clone();
        prefix.extend(
            messages[..cut]
                .iter()
                .map(|m| m.authenticate(&f.keys).unwrap()),
        );
        assert_eq!(
            client.summary.render(),
            state::fold(clause, f.context.target().causal_protocol.as_ref(), &prefix)
        );
        for message in &messages[cut..] {
            for shape in f
                .context
                .target()
                .shapes
                .iter()
                .filter(|s| s.performative == "write")
            {
                shape
                    .check(&cbcl_core::sexpr::SExpr::from(
                        message.message().innermost_simple().unwrap().clone(),
                    ))
                    .unwrap();
            }
            let step = members[0].step(message).unwrap();
            client.apply(&step, &f.context, &f.keys).unwrap();
            members[0].accept(message, &f.context, &f.keys).unwrap();
            prefix.push(message.authenticate(&f.keys).unwrap());
            assert_eq!(
                client.summary.render(),
                state::fold(clause, f.context.target().causal_protocol.as_ref(), &prefix)
            );
            let root = client.coverage;
            client.apply(&step, &f.context, &f.keys).unwrap_err();
            assert_eq!(client.coverage, root);
        }
        let state::Rule::BoundedCounter(resource) = clause.fields().last().unwrap().1 else {
            panic!("resource rule")
        };
        let observed = cbcl_core::escrow::observe(resource, &prefix);
        assert!(
            matches!(observed, cbcl_core::escrow::Outcome::Ready(_)),
            "{observed:?}"
        );
        if cut == 4 {
            use crate::host::{DurableClient, Mode};
            let directory =
                std::env::temp_dir().join(format!("cbcl-all16-recovery-{}", std::process::id()));
            let disk = DurableClient::create(&directory, client.clone(), Mode::Enabled).unwrap();
            drop(disk);
            let recovered =
                DurableClient::recover(&directory, &f.context, &f.keys, Mode::Enabled).unwrap();
            assert_eq!(recovered.client().summary, client.summary);
            assert_eq!(recovered.client().floor(), client.floor());
            drop(recovered);
            std::fs::remove_dir_all(directory).unwrap();
        }
        assert!(!client
            .summary
            .encode()
            .windows(10)
            .any(|w| w == b"discard-me"));
    }
}
