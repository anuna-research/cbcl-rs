# Verification and research records

Keep concise findings, counterexamples, review reports, result summaries and
primary-source URL/hash manifests here. Executable checks belong in `proofs/`,
`lean-cbcl/` and the Rust tests.

Build/test stdout, lint and vault snapshots, local coordination dumps, crawler
responses, downloaded papers and tool-session transcripts are generated artifacts.
They are ignored rather than committed. Mutation runners retain exit status,
assertion results and output hashes instead of full compiler/test transcripts.

Earlier reports describe the checks performed at their recorded source revision.
Their raw logs, downloaded source copies and retired single-parent Rust mutation
runners are available in Git history at commit
`713b599` (use `git rev-parse 713b599` for the full hash). Retrieve a particular
artifact with `git show 713b599:path/to/artifact`; external papers can also be
retrieved from the versioned URLs in the retained crawl manifests. Raw filenames
inside historical reports identify that archived evidence, not current dependencies.

Current runtime validation is documented in [[unified-quorum-evidence]] and
[[SPEC-031-unified-quorum-dag]]. Run:

```sh
cargo test --workspace
python3 proofs/validator-budget/check_rust_multi_parent.py
python3 proofs/validator-budget/check_rust_multi_parent_mutations.py
```

The collective Lean mutation checker is
`proofs/validator-budget/check_multi_parent_mutations.py`. Formal models, executable
counterexamples and independent review checks remain in the repository. The
retained `consensus-free-independent-review.lean` is an executable dependency of
the historical Lean protocol audit, not generated output.
