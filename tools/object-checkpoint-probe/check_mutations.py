#!/usr/bin/env python3
"""Show that semantic/security regressions fail executable tests in isolated copies."""
import json
import pathlib
import subprocess
import sys
import tempfile
import shutil

here = pathlib.Path(__file__).resolve().parent
root = here.parent.parent
source_path = "main.rs"
mutations = [
    ("forget-unseen-suppression", "if !op.delete && !suppressed {", "if !op.delete {", "delayed_creation_does_not_resurrect_a_deleted_shape"),
    ("retain-cross-key-garbage", "self.pending.retain(|(_, id)| id != &op.id);", "self.pending.remove(&(op.key.clone(), op.id.clone()));", "cross_key_arrival_order_converges_and_independent_anchors_reconcile"),
    ("accept-bad-signature", 'key.verify_strict(&encoded(d), &signature)\n            .map_err(|_| "bad signature")?;', 'let _ = (key, signature);', "omission_forgery_wrong_scope_and_unpinned_signers_reject"),
    ("skip-target-equality", "if root != snapshot.target_coverage || state.hash() != snapshot.target_summary {", "if false {", "omission_forgery_wrong_scope_and_unpinned_signers_reject"),
]
if "--admission" in sys.argv:
    source_path = "drawing.rs"
    mutations = [
        ("accept-two-of-four", "self.votes.len() < 3", "self.votes.len() < 2", "cached_policy_is_three_distinct_pinned_votes_and_context_is_immutable"),
        ("forget-covered-replay-evidence", "self.retain_evidence(step, config)?;\n            return Ok(VerificationResult::Valid);", "return Ok(VerificationResult::Valid);", "supplied_covered_replay_preserves_evidence_for_a_new_equivocation"),
        ("skip-causal-rejection", "if verdict != VerificationResult::Valid {", "if false {", "authentic_but_invalid_repeat_position_is_not_checkpoint_bypassed"),
        ("ignore-dependency-coverage-proof", "e.coverage\n                .check(self.coverage, &address(env.content_hash()))?;", "", "coverage_opening_signature_and_semantic_envelope_mutations_reject_atomically"),
    ]
if "--cached" in sys.argv:
    source_path = "drawing/cached.rs"
    mutations = [
        ("accept-mismatched-member-proposal", "if p.coverage.root() != manifest.coverage || p.state.hash() != manifest.summary {", "if false {", "independent_members_endorse_only_the_same_accepted_cut"),
        ("accept-two-cached-endorsements", "self.votes.len() < 3", "self.votes.len() < 2", "valid_content_address_does_not_authorize_a_forged_certificate"),
        ("accept-absent-floor-head", "if !p.present {", "if false {", "stale_valid_snapshot_cannot_roll_back_a_local_floor"),
        ("ignore-cache-content-address", 'digest(b"cached-checkpoint-file-v1", &bytes) != id', "false", "cache_rejects_valid_certificate_bytes_under_wrong_content_address"),
        ("discard-old-signed-bodies", "if let Some(old) = previous {", "if let Some(old) = previous.filter(|_| false) {", "warm_rebase_retains_superseded_signed_bodies_without_resupplying_them"),
        ("unbounded-tail-before-fallback", "check_offer(response)?;", "", "excessive_tail_work_is_rejected_before_cache_read_and_allows_fallback"),
        ("ignore-tail-byte-cap", "if bytes.len() > MAX_OFFER_BYTES - self.used {", "if false {", "serialized_byte_cap_is_independent_of_step_cap"),
        ("follow-canonical-cache-symlink", "libc::O_NONBLOCK | libc::O_NOFOLLOW", "libc::O_NONBLOCK", "special_files_and_symlinks_do_not_block_cache_fallback"),
    ]
source = (here / "src" / source_path).read_text()
results = []
for name, old, new, test in mutations:
    if source.count(old) != 1:
        raise SystemExit(f"Mutation location changed: {name}")
    with tempfile.TemporaryDirectory(prefix="cbcl-checkpoint-mutant-") as tmp:
        directory = pathlib.Path(tmp)
        shutil.copytree(here / "src", directory / "src")
        (directory / "Cargo.toml").write_text('''[package]
name = "cbcl-object-checkpoint-mutant"
version = "0.0.0"
edition = "2021"
[dependencies]
cbcl-core = { path = ''' + json.dumps(str(root / "crates/cbcl-core")) + ''', features = ["std", "serde"] }
serde = { version = "1", features = ["derive"] }
serde_json = "1"
sha2 = "0.10"
ed25519-dalek = "=2.1.1"
zeroize = "=1.8.2"
libc = "0.2"
[profile.dev]
debug = 0
incremental = false
''')
        (directory / "src" / source_path).write_text(source.replace(old, new))
        run = subprocess.run(["cargo", "test", "--offline", "--manifest-path", str(directory / "Cargo.toml"),
                              "--target-dir", str(root / "target/object-checkpoint-mutants"), test],
                             text=True, capture_output=True)
        killed = run.returncode != 0 and "test result: FAILED" in run.stdout
        results.append({"mutation": name, "test": test, "killed_by_test": killed,
                        "exit_code": run.returncode, "stdout": run.stdout, "stderr": run.stderr})
        if not killed:
            print(json.dumps(results, indent=2))
            raise SystemExit("Mutation survived or did not execute tests")
print(json.dumps(results, indent=2))
