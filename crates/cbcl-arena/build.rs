//! Build script for cbcl-arena.
//!
//! Captures the current git commit hash at build time and exposes it via
//! `CBCL_ARENA_GIT_COMMIT` so the reproducibility manifest can record it
//! without invoking `git` at runtime (REQ-1151).
//!
//! Falls back to `"unknown"` when git is unavailable (e.g. building from a
//! distributed source tarball).

use std::process::Command;

fn main() {
    let commit = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()
        .and_then(|o| {
            if o.status.success() {
                String::from_utf8(o.stdout).ok()
            } else {
                None
            }
        })
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "unknown".to_string());

    println!("cargo:rustc-env=CBCL_ARENA_GIT_COMMIT={commit}");
    // Re-run build.rs only when the git HEAD or this script changes. We
    // intentionally do not depend on `.git/HEAD` so that distributed builds
    // (where `.git` is absent) are not invalidated.
    println!("cargo:rerun-if-changed=build.rs");
}
