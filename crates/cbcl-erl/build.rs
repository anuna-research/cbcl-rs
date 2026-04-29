//! Build script for `cbcl-erl`.
//!
//! Sets `CBCL_RS_GIT_REVISION` for the `versions/0` NIF (SPEC-009 OBS-001).
//!
//! Resolution order:
//!   1. If we are in a git checkout and `git rev-parse HEAD` succeeds, use it.
//!   2. Otherwise, if the build environment already has `CBCL_RS_GIT_REVISION`
//!      set (e.g. set by a release script or CI), pass it through.
//!   3. Otherwise, fall back to `unknown` so source-tarball / shallow-clone
//!      builds don't panic.

use std::process::Command;

fn main() {
    // Re-run if a manual override changes, or if the workspace HEAD moves
    // (covers branch switches and new commits).
    println!("cargo:rerun-if-env-changed=CBCL_RS_GIT_REVISION");
    println!("cargo:rerun-if-changed=../../.git/HEAD");

    let revision = git_revision()
        .or_else(|| std::env::var("CBCL_RS_GIT_REVISION").ok())
        .unwrap_or_else(|| "unknown".to_string());

    println!("cargo:rustc-env=CBCL_RS_GIT_REVISION={revision}");
}

fn git_revision() -> Option<String> {
    let output = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let sha = String::from_utf8(output.stdout).ok()?.trim().to_string();
    if sha.is_empty() {
        None
    } else {
        Some(sha)
    }
}
