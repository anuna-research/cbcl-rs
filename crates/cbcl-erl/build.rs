//! Build script for `cbcl-erl`.
//!
//! Two responsibilities:
//!
//! 1. Set `CBCL_RS_GIT_REVISION` for the `versions/0` NIF (SPEC-009 OBS-001).
//!
//!    Resolution order:
//!      a. If we are in a git checkout and `git rev-parse HEAD` succeeds, use it.
//!      b. Otherwise, if the build environment already has `CBCL_RS_GIT_REVISION`
//!         set (e.g. set by a release script or CI), pass it through.
//!      c. Otherwise, fall back to `unknown` so source-tarball / shallow-clone
//!         builds don't panic.
//!
//!    Cargo's rerun-if-changed scope must cover the *actual* file that records
//!    the current commit. `.git/HEAD` typically holds `ref: refs/heads/<branch>`
//!    and does not change when commits land — only the resolved ref file
//!    (`.git/refs/heads/<branch>`) or `.git/packed-refs` does. We watch all
//!    three so a fresh commit / pull invalidates the cached build script
//!    output and `versions/0` reports a current SHA.
//!
//! 2. On macOS, set the cdylib `install_name` to `@rpath/libcbcl_erl.so`.
//!    Cargo emits `libcbcl_erl.dylib` on Darwin but `erlang:load_nif/2`
//!    appends `.so` when given a library root. Without this rewrite the
//!    NIF cannot be loaded on macOS without a manual rename/symlink.
//!    See `crates/cbcl-erl/README.md` for the install workflow.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn main() {
    // --- Git revision wiring -------------------------------------------------
    println!("cargo:rerun-if-env-changed=CBCL_RS_GIT_REVISION");

    // Workspace `.git` dir, relative to this crate's manifest dir.
    let git_dir = PathBuf::from("../../.git");

    // Always watch HEAD (covers branch switches and detached-HEAD moves).
    println!("cargo:rerun-if-changed=../../.git/HEAD");

    // Resolve the current ref file from HEAD (e.g. refs/heads/main) so we
    // re-run when a new commit lands on the checked-out branch. Also watch
    // packed-refs in case the branch ref is packed rather than loose.
    if let Some(ref_path) = head_ref_path(&git_dir) {
        // ref_path is something like "refs/heads/feat/foo".
        println!("cargo:rerun-if-changed=../../.git/{ref_path}");
    }
    println!("cargo:rerun-if-changed=../../.git/packed-refs");

    let revision = git_revision()
        .or_else(|| std::env::var("CBCL_RS_GIT_REVISION").ok())
        .unwrap_or_else(|| "unknown".to_string());

    println!("cargo:rustc-env=CBCL_RS_GIT_REVISION={revision}");

    // --- macOS NIF install_name rewrite -------------------------------------
    //
    // Erlang's `erlang:load_nif("libcbcl_erl", 0)` calls dlopen with `.so`
    // appended on every Unix-like, including Darwin. Cargo emits
    // `libcbcl_erl.dylib` and bakes that into the binary's install_name,
    // so even if the user copies the file to `libcbcl_erl.so`, dyld will
    // refuse to load it under a name that doesn't match the install_name.
    //
    // Patching the install_name to `@rpath/libcbcl_erl.so` makes the
    // resulting binary loadable under either suffix once the user
    // copies/symlinks `.dylib -> .so` (see scripts/install-mac-nif.sh
    // and the README).
    #[cfg(target_os = "macos")]
    {
        println!("cargo:rustc-cdylib-link-arg=-Wl,-install_name,@rpath/libcbcl_erl.so");

        // Surface the macOS-only post-build step to the user, with an
        // env-var escape hatch so users who have already wired up their
        // own packaging can silence the warning.
        if std::env::var_os("CBCL_ERL_SUPPRESS_MACOS_WARNING").is_none() {
            println!(
                "cargo:warning=cbcl-erl: macOS produces libcbcl_erl.dylib but \
                 erlang:load_nif/2 expects libcbcl_erl.so — run \
                 crates/cbcl-erl/scripts/install-mac-nif.sh after build, or \
                 set CBCL_ERL_SUPPRESS_MACOS_WARNING=1 to silence."
            );
        }
    }
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
    if sha.is_empty() { None } else { Some(sha) }
}

/// Parse `.git/HEAD` and return the ref path it points at, e.g.
/// `refs/heads/main`. Returns `None` if HEAD is detached, the file is
/// missing (shallow clone, source tarball), or the contents are malformed.
fn head_ref_path(git_dir: &Path) -> Option<String> {
    let head = fs::read_to_string(git_dir.join("HEAD")).ok()?;
    let trimmed = head.trim();
    let rest = trimmed.strip_prefix("ref:")?.trim();
    if rest.is_empty() {
        None
    } else {
        Some(rest.to_string())
    }
}
