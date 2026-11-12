//! SPEC-043 TEST-4308: public key inspection at the CLI boundary.
use std::process::Command;

#[test]
fn inspect_public_key_without_claiming_authorization() {
    let text = "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu";
    let output = Command::new(env!("CARGO_BIN_EXE_cbcl-cli"))
        .args(["multikey", text])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let json: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(json["multikey"], text);
    assert_eq!(json["codec"], 0xed);
    assert_eq!(json["public_key"].as_array().unwrap().len(), 32);
    assert_eq!(json["signing_identity"], format!("@ed25519:{text}"));
}

#[test]
fn malformed_key_cannot_produce_public_key_output() {
    let output = Command::new(env!("CARGO_BIN_EXE_cbcl-cli"))
        .args(["multikey", "z0"])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
}
