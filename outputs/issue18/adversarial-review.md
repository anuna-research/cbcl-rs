# Issue 18 independent adversarial review

Result: no unresolved blocking findings in the stable integration reviewed on 2026-10-06. Scope is `latest-per-signer` only. Source review used SPEC-019, IMPL-019, the worktree diff, and Elephant's `issue18-review` acceptance/dependencies; no implementation sources were modified.

- Signer selection removes only addresses named by domain-admitted writes of the same verb and signer. Cross-signer, cross-verb, and excluded replacers cannot retire a ballot. Concurrent surviving writes still select greatest address.
- Binder uses that same domain-filtered current selection, includes all own concurrent writes, supplies an empty first-write list, and rejects caller bookkeeping. Mixed replacement rules retain a sorted distinct bounded union. Incremental prefix truncation is equivalent to truncating the full union.
- Compiler insertion, required receipt bookkeeping, shared exports, JavaScript authoring, and Erlang fixtures agree. Caller intent fields omit bookkeeping; canonical replacement writers include it.
- `Last`'s implementation branch and Lean definition retain address ordering. The dedicated regression verifies a lower-address signer edit wins its ballot while `last` still returns the higher-address old value.
- Lean's signer selection and binder match the intended abstract semantics. Domain prefiltering and omission of Rust's finite prefix are explicitly documented; Rust/Lean correspondence remains evidence, not a refinement theorem. Reviewed successful build/allowlisted-axiom audit logs.
- Corpus pin and spec major version are 1.0.0. Migration keeps old histories under the old runtime. New canonical vectors exercise lower-address edits, concurrency, hostile signer references, and history preservation.

Two documentation findings were raised and corrected before final review: the finite prefix is checked by the corpus **and targeted Rust tests**, and the README's new-act currency claim now requires freshness and no prior reference to its address.

Independent final validation: `cargo test -p cbcl-core --test state_properties signer_` passed all 8 tests; `git diff --check` passed. Reviewed mutation evidence showing removal of signer ownership fails the ownership regression, followed by restored full core tests passing. Elephant derives `ready(issue18-review)` from completed core, surfaces, and Lean tasks.

This review does not certify the still-running full-workspace gate or serve as the separate orientation-only comprehension review. Coordinator may record completion of `issue18-review` against this artifact.
