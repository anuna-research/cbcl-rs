//! Tests for `cbcl-cli verify`'s R5 surface.
//!
//! Run with: cargo test --test verify_r5 -p cbcl-cli
//!
//! These exercise the binary end-to-end (stdin → stdout/stderr +
//! exit code) so the test fixes both the R5 behaviour and its
//! reporting format.

use std::io::Write;
use std::process::{Command, Stdio};

const BIN: &str = env!("CARGO_BIN_EXE_cbcl-cli");

struct Output {
    code: i32,
    stdout: String,
    stderr: String,
}

fn run_verify(input: &str) -> Output {
    let mut child = Command::new(BIN)
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
    let out = child.wait_with_output().expect("wait cbcl-cli");

    Output {
        code: out.status.code().unwrap_or(-1),
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
    }
}

const NO_PROTOCOL: &str = r#"
(define test-no-protocol (cbcl) @test
  (:resource-requirements
    ((max-depth 4) (max-expansion-size 64) (verification-time 50)))
  (extend foo (x)
    (tell @peer (foo-form :x x))))
"#;

const VALID_PROTOCOL: &str = r#"
(define test-valid-protocol (cbcl) @test
  (:resource-requirements
    ((max-depth 4) (max-expansion-size 64) (verification-time 50)))
  (extend foo (x)
    (tell @peer (foo-form :x x)))
  (extend bar (y)
    (tell @peer (bar-form :y y)))
  (protocol
    (then begin foo bar)))
"#;

const CYCLIC_PROTOCOL: &str = r#"
(define test-cyclic (cbcl) @test
  (:resource-requirements
    ((max-depth 4) (max-expansion-size 64) (verification-time 50)))
  (extend foo (x)
    (tell @peer (foo-form :x x)))
  (extend bar (y)
    (tell @peer (bar-form :y y)))
  (protocol
    (then begin foo bar)
    (then bar foo)))
"#;

const UNDEFINED_PERF: &str = r#"
(define test-undefined (cbcl) @test
  (:resource-requirements
    ((max-depth 4) (max-expansion-size 64) (verification-time 50)))
  (extend foo (x)
    (tell @peer (foo-form :x x)))
  (protocol
    (then begin foo missing)))
"#;

#[test]
fn verify_succeeds_without_protocol_and_omits_r5_from_summary() {
    let out = run_verify(NO_PROTOCOL);
    assert_eq!(out.code, 0, "stderr: {}", out.stderr);
    assert!(
        out.stdout.contains("(R1, R2, R3)") && !out.stdout.contains("R5"),
        "stdout: {}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("protocol steps"),
        "stdout: {}",
        out.stdout
    );
}

#[test]
fn verify_succeeds_with_valid_protocol_and_reports_r5_and_step_count() {
    let out = run_verify(VALID_PROTOCOL);
    assert_eq!(out.code, 0, "stderr: {}", out.stderr);
    assert!(
        out.stdout.contains("(R1, R2, R3, R5)"),
        "stdout: {}",
        out.stdout
    );
    assert!(
        out.stdout.contains("protocol steps:"),
        "stdout: {}",
        out.stdout
    );
}

#[test]
fn verify_fails_on_protocol_cycle() {
    let out = run_verify(CYCLIC_PROTOCOL);
    assert_eq!(out.code, 1, "stdout: {}", out.stdout);
    assert!(
        out.stderr.contains("R5:") && out.stderr.contains("cycle"),
        "stderr: {}",
        out.stderr
    );
}

#[test]
fn verify_fails_on_undefined_performative_in_protocol() {
    let out = run_verify(UNDEFINED_PERF);
    assert_eq!(out.code, 1, "stdout: {}", out.stdout);
    assert!(
        out.stderr.contains("R5:") && out.stderr.contains("undefined"),
        "stderr: {}",
        out.stderr
    );
}
