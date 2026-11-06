---
title: Register semantics implementation review
mode: explanation
status: verified-component-extension
last-updated: 2026-11-06
---

# Register semantics implementation review

[[SPEC-035-register-semantics#ADR-3502]] records the user's selection of an additive
trusted-host HLC profile. Existing rules retain their old hash arbitration.
The branch is `draft/state-register-semantics`, based on main `45bd3d0`.

## Scope

The implementation includes the rule parser, R7 installation and message-local
clock recognition, pure HLC helpers, fold arbitration, binder replacements,
canonical body encoding, schemas, description, JSON authoring and JavaScript sugar.
Multi-value names are aliases whose canonical old heads preserve equivalent identity.
No owned-register operator, alternate clock profile or resource-policy change is added.

The HLC Lean model proves greatest-candidate soundness/completeness, set invariance
and composition with existing signer/keyed candidate selection. It consumes typed
clock evidence and an order-preserving signer abstraction. Clock honesty, wire/Rust
correspondence and the general whole-kernel clause theorem remain outside that proof.

## Executed evidence

The first end-to-end new-rule test failed at the old parser's unknown-head error
before implementation, then passed. Rust core/parser suites pass. The native corpus
and shared state frames pass with the HLC vector and corpus version 3.0.0.
The TypeScript check and JavaScript/WASM suite pass, including the new authoring
operations and corpus. The full Lean build, environment lint and central axiom audit pass. Isolated
semantic mutations fail their corresponding executed Rust assertions or the
independent Lean maximum proof. The commands and captured summaries are in
`proofs/register-semantics/implementation-checks.json`; mutation diagnostics are
in `proofs/register-semantics/hlc-mutations.json`.

Legacy identity expectations were generated with the unmodified parser in a
separate detached worktree at main `45bd3d0`. They are checked by the new regression
and recorded in `proofs/register-semantics/legacy-dialect-identities.json`.
All existing vector contents remain unchanged.

## Host and claim boundaries

An HLC field's canonical shape does not establish honest time. A regression shows
an authorized malicious writer's far-future clock wins LWW arbitration. Hosts
supply, merge and persist clock evidence; the core reads no system clock. Checked
helpers refuse logical overflow without wrapping. Resource certification retains
its separate Byzantine fault assumptions and is not weakened by this profile.


## Review and discovered defect

Independent source reviewer `/root/hlc_implementation_review` found a domain-source
mismatch in the shared binder helper: an excluded same-key replacer could hide
an admitted candidate from replacement/deletion binding while the fold retained it.
The dedicated regression was observed failing before repair. The binder now calls
the fold's domain-aware current selector in both directions. The regression and
its JavaScript/WASM counterpart pass. The reviewer re-examined the fix and found
no remaining blocker. This also corrects the same existing keyed-register and
observed-set binder defect; old canonical identities and declared contracts remain
unchanged. Existing corpus files are unchanged apart from the explicit VERSION
advance, and the old identity golden test passes.

Independent proof reviewer `/root/hlc_proof_review` found no blocking proof or
claim issue. It checked independence of maximality, nonvacuity of the unconditional
soundness theorem, use of consistency only for uniqueness, candidate-source scope
and the explicit clock/signer/wire/Rust boundaries. The broader clause theorem is
not claimed complete. These are independent tool-session reviews, not separately
signed Elephant peer attestations or human deployment approval.

Fresh-context reader `/root/hlc_orientation_check` read only Orientation and
correctly predicted legacy hash ordering, opt-in host-HLC rules, uncertified writer
timestamps, conflict-preserving alternatives and the still-open full-kernel target.
It identified ADR-3502 as the adopted mechanism. No material ambiguity was reported.

## Reproduction and limitations

Run the Rust suites with `cargo test -p cbcl-core -p cbcl-parser --locked`.
Run workspace and no-default-feature checks separately. Build WASM with the
wasm-bindgen CLI version pinned by Cargo.lock, then run the TypeScript check and
JavaScript suite. After the binder repair, the relevant HLC and full corpus JS
cases were rerun against freshly rebuilt WASM. The earlier full JS suite also
passed; unrelated progress tests were not repeated after the local binder repair.

Run `lake build`, `lake exe runLinter LeanCbcl` and `scripts/check-axioms.sh`.
Run `python3 scripts/check-hlc-register-mutations.py --output <report.json>` for
isolated Rust and model mutants. Mutation builds use a private target directory,
so mutant artifacts cannot replace the normal test binaries. An initial shared
build-cache approach produced unreliable concurrent verification; it was replaced,
the affected normal package artifacts were cleaned, and final Rust suites plus
isolated mutation checks passed. Temporary disk exhaustion interrupted earlier
build attempts; final workspace and no-default-feature checks completed afterward.

Repository-wide zetl validation retains the baseline dead-link and SPL errors,
with no new dead links or SPL errors from this change. New implementation links
and heading anchors were checked separately. Updated SPEC-035 controlled-language
and new explanation-mode documentation checks pass. Historical draft validation
is [[register-semantics-draft-review]], not current implementation evidence.

The common state-frame corpus validates shared semantics used by WASM, FFI and
Erlang adapters. Workspace compilation covers all adapters; native Erlang loading
and a deployed cross-device clock service are not asserted. The standard suite's
ignored/depth tests remain ignored and are recorded in the captured summaries.
