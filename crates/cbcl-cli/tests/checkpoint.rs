//! `cbcl checkpoint` end-to-end (SPEC-035 TEST-3509, CON-3505). One process
//! per operation; two real proofs in total.
#![cfg(feature = "state-proof")]

use serde_json::{json, Value};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const WARNING: &str = "warning: candidates are unauthenticated; signer labels are host-asserted";

struct Run {
    code: i32,
    stdout: String,
    stderr: String,
}

fn checkpoint(args: &[&str]) -> Run {
    let Output {
        status,
        stdout,
        stderr,
    } = Command::new(env!("CARGO_BIN_EXE_cbcl-cli"))
        .env("RAYON_NUM_THREADS", "2")
        .arg("checkpoint")
        .args(args)
        .output()
        .expect("spawn cbcl-cli");
    let run = Run {
        code: status.code().expect("exit code"),
        stdout: String::from_utf8(stdout).expect("utf-8 stdout"),
        stderr: String::from_utf8(stderr).expect("utf-8 stderr"),
    };
    assert!(
        run.stderr.lines().any(|l| l == WARNING),
        "missing warning line in stderr: {}",
        run.stderr
    );
    run
}

fn fixture_profile() -> Value {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../test-vectors/state/signer-supersession.json");
    let v: Value = serde_json::from_slice(&fs::read(path).expect("fixture")).expect("json");
    let candidates: Vec<Value> = v["messages"].as_array().expect("messages")[..3]
        .iter()
        .map(|m| json!({"text": m["canonical"], "label": m["signer"]}))
        .collect();
    json!({"dialect": v["contract"], "thread": "s1", "candidates": candidates})
}

// Native IDs, independent of the profile's lexicographic bit assignment.
fn fixture_addresses() -> Vec<String> {
    fixture_profile()["candidates"]
        .as_array()
        .unwrap()
        .iter()
        .map(|c| {
            let ast = cbcl_parser::parse(c["text"].as_str().unwrap()).unwrap();
            let message = cbcl_parser::parse_message(&ast).unwrap();
            cbcl_core::state::Act::from_message(message, c["label"].as_str().unwrap())
                .unwrap()
                .address
        })
        .collect()
}

fn temp_dir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("cbcl-checkpoint-{}-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("temp dir");
    dir
}

fn write(dir: &Path, name: &str, v: &Value) -> String {
    let path = dir.join(name);
    fs::write(&path, serde_json::to_vec(v).unwrap()).expect("write");
    path.to_string_lossy().into_owned()
}

/// Golden identity and every valid mask are pinned in
/// `test-vectors/state-proof/signer-supersession.json` (TEST-3505).
fn golden() -> Value {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../test-vectors/state-proof/signer-supersession.json");
    serde_json::from_slice(&fs::read(path).expect("golden")).expect("json")
}

#[test]
fn compile_prove_verify_and_chain_verify_round_trip() {
    let dir = temp_dir("roundtrip");
    let profile = write(&dir, "profile.json", &fixture_profile());

    // compile: identity and three addresses, in bit order.
    let run = checkpoint(&["compile", &profile]);
    assert_eq!(run.code, 0, "{}", run.stderr);
    let out: Value = serde_json::from_str(run.stdout.trim()).expect("compact json");
    assert_eq!(out["profile"], golden()["profile"]);
    let addresses: Vec<String> = out["addresses"]
        .as_array()
        .expect("addresses")
        .iter()
        .map(|a| a.as_str().unwrap().to_owned())
        .collect();
    assert_eq!(addresses.len(), 3);
    assert!(addresses
        .iter()
        .all(|a| a.starts_with("sha256-") && a.len() == 71));
    assert!(!run.stdout.contains('\n') || run.stdout.trim().lines().count() == 1);

    // Select semantic fixture cuts; HLC edits may change sorted bit positions.
    let native = fixture_addresses();
    let opener = native[0].clone();
    let two = format!("{},{}", native[0], native[1]);
    let two_mask = addresses
        .iter()
        .enumerate()
        .filter(|(_, id)| native[..2].contains(id))
        .fold(0usize, |mask, (bit, _)| mask | (1 << bit))
        .to_string();
    let all = addresses.join(",");

    // prove twice: genesis -> opener, opener -> two. Written to files.
    let p1 = dir.join("p1.json").to_string_lossy().into_owned();
    let run = checkpoint(&[
        "prove", &profile, "--before", "-", "--after", &opener, "--out", &p1,
    ]);
    assert_eq!(run.code, 0, "{}", run.stderr);
    assert_eq!(run.stdout, "", "prove with --out writes nothing to stdout");
    let p2 = dir.join("p2.json").to_string_lossy().into_owned();
    let run = checkpoint(&[
        "prove", &profile, "--before", &opener, "--after", &two, "--out", &p2,
    ]);
    assert_eq!(run.code, 0, "{}", run.stderr);

    // verify: receiver-derived statement matches, exit 0; the after
    // checkpoint is printed as hex (CON-3505), equal to the independently pinned golden cut.
    let run = checkpoint(&[
        "verify", &profile, &p2, "--before", &opener, "--after", &two,
    ]);
    assert_eq!(run.code, 0, "{}", run.stderr);
    let out: Value = serde_json::from_str(run.stdout.trim()).expect("verify json");
    assert_eq!(out["verified"], json!(true));
    assert_eq!(
        out["after"],
        golden()["checkpoints"][&two_mask],
        "{}",
        run.stdout
    );

    // verify with a different --after (a valid identity transition): exit 1.
    let run = checkpoint(&[
        "verify", &profile, &p2, "--before", &opener, "--after", &opener,
    ]);
    assert_eq!(run.code, 1, "stdout: {} stderr: {}", run.stdout, run.stderr);

    // verify with a different --after naming a non-identity valid statement: exit 1.
    let run = checkpoint(&["verify", &profile, &p1, "--before", "-", "--after", &two]);
    assert_eq!(run.code, 1);

    // chain-verify: hand-built chain of the two proofs from genesis.
    let proof1: Value = serde_json::from_slice(&fs::read(&p1).unwrap()).unwrap();
    let proof2: Value = serde_json::from_slice(&fs::read(&p2).unwrap()).unwrap();
    let chain =
        json!({"profile": proof1["statement"]["profile"], "links": [proof1, proof2.clone()]});
    let chain_path = write(&dir, "chain.json", &chain);
    let run = checkpoint(&["chain-verify", &profile, &chain_path]);
    assert_eq!(run.code, 0, "{}", run.stderr);
    let final_cp: Value = serde_json::from_str(run.stdout.trim()).expect("checkpoint json");
    assert_eq!(
        final_cp,
        golden()["checkpoints"][&two_mask],
        "{}",
        run.stdout
    );
    assert!(final_cp["accepted"].as_str().is_some_and(|h| h.len() == 64));

    // chain-verify with --start and --end naming the right sets: exit 0.
    let run = checkpoint(&[
        "chain-verify",
        &profile,
        &chain_path,
        "--start",
        "-",
        "--end",
        &two,
    ]);
    assert_eq!(run.code, 0, "{}", run.stderr);

    // chain-verify with a wrong --end or wrong --start: exit 1.
    let run = checkpoint(&["chain-verify", &profile, &chain_path, "--end", &all]);
    assert_eq!(run.code, 1);
    let run = checkpoint(&["chain-verify", &profile, &chain_path, "--start", &opener]);
    assert_eq!(run.code, 1);

    // chain-verify on a chain with a link order swap: exit 1.
    let swapped =
        json!({"profile": chain["profile"], "links": [chain["links"][1], chain["links"][0]]});
    let swapped_path = write(&dir, "swapped.json", &swapped);
    let run = checkpoint(&["chain-verify", &profile, &swapped_path]);
    assert_eq!(run.code, 1);

    // Same-shape mutations exercise transcript verification and caller-state binding.
    let mut corrupt = proof2.clone();
    let byte = corrupt["transcript"][0].as_u64().unwrap();
    corrupt["transcript"][0] = json!(byte ^ 1);
    let path = write(&dir, "corrupt-transcript.json", &corrupt);
    assert_eq!(
        checkpoint(&["verify", &profile, &path, "--before", &opener, "--after", &two]).code,
        1
    );
    let mut forged = proof2.clone();
    let byte = forged["statement"]["after"]["state"][0].as_u64().unwrap();
    forged["statement"]["after"]["state"][0] = json!(byte ^ 1);
    let path = write(&dir, "forged-state.json", &forged);
    assert_eq!(
        checkpoint(&["verify", &profile, &path, "--before", &opener, "--after", &two]).code,
        1
    );

    // a proof package with an unknown member is rejected before verification.
    let mut bad = proof2.clone();
    bad["extra"] = json!(1);
    let bad_path = write(&dir, "bad-proof.json", &bad);
    let run = checkpoint(&[
        "verify", &profile, &bad_path, "--before", &opener, "--after", &two,
    ]);
    assert_eq!(run.code, 1);

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn malformed_profile_and_address_inputs_exit_one() {
    let dir = temp_dir("malformed");

    // unknown member in profile.json
    let mut unknown = fixture_profile();
    unknown["extra"] = json!(true);
    let path = write(&dir, "unknown.json", &unknown);
    let run = checkpoint(&["compile", &path]);
    assert_eq!(run.code, 1, "{}", run.stdout);
    assert_eq!(run.stdout, "");

    // unknown member inside a candidate
    let mut inner = fixture_profile();
    inner["candidates"][0]["signer"] = json!("@x");
    let path = write(&dir, "inner.json", &inner);
    assert_eq!(checkpoint(&["compile", &path]).code, 1);

    // missing file, non-JSON file, oversize file
    let missing = dir.join("absent.json").to_string_lossy().into_owned();
    assert_eq!(checkpoint(&["compile", &missing]).code, 1);
    let garbage = dir.join("garbage.json");
    fs::write(&garbage, b"{\"dialect\": ").unwrap();
    assert_eq!(checkpoint(&["compile", &garbage.to_string_lossy()]).code, 1);
    let big = dir.join("big.json");
    fs::write(&big, vec![b' '; (1 << 20) + 1]).unwrap();
    assert_eq!(checkpoint(&["compile", &big.to_string_lossy()]).code, 1);

    // malformed and unknown addresses
    let profile = write(&dir, "profile.json", &fixture_profile());
    let bogus = format!("sha256-{}", "0".repeat(64));
    let run = checkpoint(&["prove", &profile, "--before", "-", "--after", &bogus]);
    assert_eq!(run.code, 1);
    let run = checkpoint(&[
        "prove",
        &profile,
        "--before",
        "-",
        "--after",
        "not-an-address",
    ]);
    assert_eq!(run.code, 1);
    let run = checkpoint(&["prove", &profile, "--before", "-", "--after", ""]);
    assert_eq!(run.code, 1);

    // a repeated address in one list is a rejection (CON-3505).
    let run = checkpoint(&["compile", &profile]);
    let out: Value = serde_json::from_str(run.stdout.trim()).unwrap();
    let opener = fixture_addresses()[0].clone();
    assert!(out["addresses"]
        .as_array()
        .unwrap()
        .contains(&json!(opener)));
    let twice = format!("{opener},{opener}");
    let run = checkpoint(&["prove", &profile, "--before", "-", "--after", &twice]);
    assert_eq!(run.code, 1, "{}", run.stdout);
    assert!(run.stderr.contains("repeated address"), "{}", run.stderr);

    // a positional array where an object is required (CON-3505): top level
    // and one candidate.
    let f = fixture_profile();
    let top = json!([f["dialect"], f["thread"], f["candidates"]]);
    let path = write(&dir, "top-array.json", &top);
    assert_eq!(checkpoint(&["compile", &path]).code, 1);
    let mut cand = fixture_profile();
    let c0 = cand["candidates"][0].clone();
    cand["candidates"][0] = json!([c0["text"], c0["label"]]);
    let path = write(&dir, "candidate-array.json", &cand);
    assert_eq!(checkpoint(&["compile", &path]).code, 1);

    // a profile file of exactly 1 MiB is read and accepted.
    let mut bytes = serde_json::to_vec(&fixture_profile()).unwrap();
    bytes.resize(1 << 20, b' ');
    let at_limit = dir.join("at-limit.json");
    fs::write(&at_limit, &bytes).unwrap();
    assert_eq!(
        checkpoint(&["compile", &at_limit.to_string_lossy()]).code,
        0
    );

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn usage_errors_exit_two() {
    let out = Command::new(env!("CARGO_BIN_EXE_cbcl-cli"))
        .args(["checkpoint", "prove", "x.json", "--before", "-"])
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(2));
    let out = Command::new(env!("CARGO_BIN_EXE_cbcl-cli"))
        .args(["checkpoint", "frobnicate"])
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(2));
}
