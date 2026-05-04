//! End-to-end coverage for `cbcl verify`, including the R5 (causal-protocol +
//! shape coherence) wiring added by REQ-516. Locks down both the CLI plumbing
//! and the R5-relevant content of the bundled `dialects/*.cbcl` fixtures.

use std::path::PathBuf;
use std::process::{Command, Stdio};

fn cli() -> Command {
    Command::new(env!("CARGO_BIN_EXE_cbcl-cli"))
}

fn dialect_path(name: &str) -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest.join("..").join("..").join("dialects").join(name)
}

fn run_verify_on_input(input: &str) -> (i32, String, String) {
    use std::io::Write;
    let mut child = cli()
        .arg("verify")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn cbcl-cli");
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();
    let out = child.wait_with_output().expect("wait_with_output");
    (
        out.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

fn run_verify_on_fixture(name: &str) -> (i32, String, String) {
    let input =
        std::fs::read_to_string(dialect_path(name)).unwrap_or_else(|e| panic!("read {name}: {e}"));
    run_verify_on_input(&input)
}

// ---------------------------------------------------------------------------
// Substantive R5: crosschain dialect declares a (protocol …) clause.
// ---------------------------------------------------------------------------

#[test]
fn crosschain_passes_r5_with_protocol() {
    let (code, stdout, stderr) = run_verify_on_fixture("crosschain.cbcl");
    assert_eq!(code, 0, "non-zero exit; stderr=\n{stderr}");
    assert!(
        stdout.contains("(R1, R2, R3, R5)"),
        "summary line missing R5 mention; stdout=\n{stdout}"
    );
    assert!(
        stdout.contains("R5: pass"),
        "missing 'R5: pass' line; stdout=\n{stdout}"
    );
    // Anchor the dialect's R5-relevant content: the protocol references seven
    // extended performatives. Catches accidental deletion of the (protocol …)
    // clause OR of any of the seven `extend` declarations the protocol
    // references.
    assert!(
        stdout.contains("performatives: 7"),
        "expected 7 performatives; stdout=\n{stdout}"
    );
    assert!(
        stdout.contains("cbcl-crosschain-transfer"),
        "expected dialect name; stdout=\n{stdout}"
    );
}

// ---------------------------------------------------------------------------
// Vacuous R5: dialects without (protocol …) or (shape …) still report pass.
// ---------------------------------------------------------------------------

#[test]
fn protocol_free_dialects_pass_r5_vacuously() {
    for fixture in [
        "email.cbcl",
        "planning.cbcl",
        "artifacts.cbcl",
        "precision-agriculture.cbcl",
    ] {
        let (code, stdout, stderr) = run_verify_on_fixture(fixture);
        assert_eq!(code, 0, "{fixture}: non-zero exit; stderr=\n{stderr}");
        assert!(
            stdout.contains("(R1, R2, R3, R5)"),
            "{fixture}: summary line missing R5 mention; stdout=\n{stdout}"
        );
        assert!(
            stdout.contains("R5: pass"),
            "{fixture}: missing 'R5: pass' line; stdout=\n{stdout}"
        );
    }
}

// ---------------------------------------------------------------------------
// Negative R5: synthetic dialect whose (protocol …) clause references a
// performative that the dialect does not define. R5 must surface this; the
// CLI must exit non-zero with an `R5:` violation in stderr.
// ---------------------------------------------------------------------------

#[test]
fn protocol_referencing_undefined_performative_fails_r5() {
    // `step-undefined` is not declared as an `extend`, so the protocol's
    // `(then begin step-undefined)` violates R5 §REQ-206 (performative
    // definedness).
    let dialect = r#"
(define cbcl-r5-negative-undefined (cbcl) @test-author
  (:resource-requirements
    ((max-depth 8)
     (max-expansion-size 256)
     (verification-time 20)))

  (extend step-defined (payload)
    (tell @sink (carry :payload payload) :domain test))

  (protocol
    (then begin step-undefined)
    (then step-undefined step-defined)))
"#;

    let (code, stdout, stderr) = run_verify_on_input(dialect);
    assert_ne!(
        code, 0,
        "expected non-zero exit on R5 violation; stdout=\n{stdout}\nstderr=\n{stderr}"
    );
    assert!(
        stderr.contains("R5:"),
        "expected R5 violation in stderr; stderr=\n{stderr}"
    );
    // The CLI should NOT print the success summary on a failed verify.
    assert!(
        !stdout.contains("R5: pass"),
        "unexpected 'R5: pass' on failed verify; stdout=\n{stdout}"
    );
}
