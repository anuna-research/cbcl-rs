use checkpoint_common::{compute, Input};
use checkpoint_methods::CHECKPOINT_GUEST_ELF;
use risc0_zkvm::{default_executor, ExecutorEnv, ExitCode};
fn main() {
    let base: Input =
        serde_json::from_slice(&std::fs::read("fixtures/drawing-1.json").unwrap()).unwrap();
    let mut cases = Vec::new();
    let mut changed = base.clone();
    changed.thread = "wrong".into();
    cases.push(("wrong-thread", serde_json::to_vec(&changed).unwrap()));
    let mut changed = base.clone();
    changed.messages[1].canonical = format!("(lang wrong {})", changed.messages[1].canonical);
    cases.push((
        "nested-wrong-dialect",
        serde_json::to_vec(&changed).unwrap(),
    ));
    let mut changed = base.clone();
    changed.messages.push(changed.messages[0].clone());
    cases.push(("duplicate", serde_json::to_vec(&changed).unwrap()));
    let mut changed = base.clone();
    changed.messages.remove(0);
    cases.push(("pending", serde_json::to_vec(&changed).unwrap()));
    let mut changed = base.clone();
    changed.messages[0].canonical.push(' ');
    cases.push(("noncanonical", serde_json::to_vec(&changed).unwrap()));
    let mut changed = base.clone();
    changed.dialect = "(bad)".into();
    cases.push(("invalid-dialect", serde_json::to_vec(&changed).unwrap()));
    let mut changed = base.clone();
    changed.messages[1].canonical = changed.messages[1]
        .canonical
        .replace(":data (", ":bad-data (");
    cases.push(("invalid-shape", serde_json::to_vec(&changed).unwrap()));
    cases.push(("invalid-json", b"{\"extra\":true}".to_vec()));
    let mut role:Input=serde_json::from_slice(&std::fs::read("fixtures/checklist-role.json").unwrap()).unwrap();
    role.messages[2].signer="@outside-cast".into();
    role.messages[2].canonical=role.messages[2].canonical.replace("signed @bo ","signed @outside-cast ").replace(":from @bo",":from @outside-cast");
    cases.push(("sender-outside-cast",serde_json::to_vec(&role).unwrap()));
    let mut ancestor:Input=serde_json::from_slice(&std::fs::read("fixtures/ancestor-status.json").unwrap()).unwrap();
    let parent="(define checkpoint-parent (cbcl) @author (:resource-requirements ((max-depth 16) (max-expansion-size 4096) (verification-time 1000))) (extend parent-tell (to value) (tell to value)))";
    assert_eq!(ancestor.dialect.matches(parent).count(),1);
    ancestor.dialect=ancestor.dialect.replace(parent,"");
    cases.push(("missing-required-ancestor",serde_json::to_vec(&ancestor).unwrap()));
    // A valid control must execute successfully before negative outcomes count.
    let control = serde_json::to_vec(&base).unwrap();
    let expected_control = compute(&control).unwrap().journal;
    let mut builder = ExecutorEnv::builder();
    builder
        .write(&(control.len() as u32))
        .unwrap()
        .write_slice(&control)
        .segment_limit_po2(18);
    let valid = default_executor()
        .execute(builder.build().unwrap(), CHECKPOINT_GUEST_ELF)
        .expect("valid control failed: infrastructure or image problem");
    let actual: checkpoint_common::Journal = valid.journal.decode().unwrap();
    assert_eq!(actual, expected_control);
    assert_eq!(valid.exit_code, ExitCode::Halted(0));
    let mut results = Vec::new();
    for (name, bytes) in cases {
        let expected_error = compute(&bytes)
            .err()
            .expect("negative fixture must be invalid");
        let mut stderr = Vec::new();
        let result = {
            let mut b = ExecutorEnv::builder();
            b.write(&(bytes.len() as u32))
                .unwrap()
                .write_slice(&bytes)
                .stderr(&mut stderr)
                .segment_limit_po2(18)
                .session_limit(Some(32 * 1024 * 1024));
            default_executor().execute(b.build().unwrap(), CHECKPOINT_GUEST_ELF)
        };
        let detail = match result {
            Err(e) => e.to_string(),
            Ok(session) => {
                assert_ne!(
                    session.exit_code,
                    ExitCode::Halted(0),
                    "invalid guest input accepted: {name}"
                );
                format!("{:?}", session.exit_code)
            }
        };
        let combined = format!("{} {}", detail, String::from_utf8_lossy(&stderr));
        assert!(
            combined.contains("invalid checkpoint input") && combined.contains(&expected_error),
            "inconclusive infrastructure/resource error for {name}: {combined}"
        );
        results.push(serde_json::json!({"case":name,"guest_rejected":true,"detail":detail}));
    }
    std::fs::write(
        "evidence/guest-negative-results.json",
        serde_json::to_vec_pretty(&results).unwrap(),
    )
    .unwrap();
    println!("{}", serde_json::to_string(&results).unwrap());
}
