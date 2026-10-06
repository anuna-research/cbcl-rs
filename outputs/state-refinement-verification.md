# State refinement verification

Branch: `state-rules-spec`. Implementation: [StateRefinement.lean](../lean-cbcl/LeanCbcl/StateRefinement.lean).
Specification: [SPEC-019](../specs/SPEC-019-state-rules.md), REQ-1935–1938,
CON-1906, ADR-1913, TEST-1954–1959.
Executable plan: [IMPL-020](../plans/IMPL-020-state-refinement.spl).

## Result

Kernel-checked forward simulation from a typed execution machine into an
independently specified business machine. The observation reads accepted acts.
Fresh acceptance proves the labelled business operation; internal activity and
reapplication preserve the observation. Finite reachability and infinite,
time-indexed behavior mapping are proved without erasing stuttering.

The worked instance reuses the existing counter fold, with a separate business
machine defining integer addition and subtraction. This is not an abstract
`next` defined by the fold or by the concrete execution relation.

## Gates and evidence

| Gate | Result | Evidence |
| --- | --- | --- |
| `lake build` in `lean-cbcl` | Pass | [build log](state-refinement-build.log) |
| `lake exe runLinter LeanCbcl` | Pass | [lint log](state-refinement-lint.log) |
| `scripts/check-axioms.sh` | Pass; standard allowlist only | [axiom log](state-refinement-axioms.log) |
| New SPEC-019 identifier uniqueness and internal trace targets | Pass | [trace log](state-refinement-trace.log) |
| Counter subtraction-to-addition mutation | Rejected by simulation and regression | [mutation log](state-refinement-mutation.log) |
| Independent adversarial review | Accept; all findings resolved | [review](state-refinement-review.md) |
| `git diff --check` | Pass | Local changed-path inspection |
| Concept documentation-mode and controlled-language lint | Pass | `usdd-lint.sh --doc/--type descriptive --strict` |
| Repository-wide `zetl -d . check --dead-links --fail-on error` | Fail: unrelated link debt | [vault log](state-refinement-vault.log) |

The vault reports 25 dead links outside the new refinement section and concept,
with zero syntax or SPL errors. The unrelated links were not repaired here.
The existing `check-verified-by.sh` passes but covers SPEC-002/003, not the new
SPEC-019 obligations; it is not counted as refinement traceability evidence.

TEST-1954: reachable address uniqueness, received membership, authentication.
TEST-1955: initial state, step simulation, reachability, infinite behaviors,
fresh-acceptance effect, and rejection of constant-observation/False-next vacuity.
TEST-1956: counter insertion effect and counter behavior refinement.
TEST-1957: absent candidates, pending predecessors, and conflicting addresses.
TEST-1958: duplicate insertion, subtraction sign, receipt without acceptance,
and a deliberate mutation of the independent decrement equation.
TEST-1959: fresh read-only cross-model review and claim-boundary inspection.

## Scope inspection

Tracked changes are confined to the two READMEs, SPEC-019, LeanCbcl's import,
and the axiom audit. New implementation files are `StateRefinement.lean`,
`docs/concepts/state-refinement.md`, and `plans/IMPL-020-state-refinement.spl`.
New evidence and the local Elephant store live under `outputs/state-refinement*`.
No Rust, transport, parser, cryptographic, dialect, or deployed-system code changed.
Unrelated untracked workspace files were preserved.

A search for `Rust|fairness|authentic|independent|stutter` across the proof,
Lean README, and concept checked the documented boundaries against assumptions.
Authentication is a premise on typed acts, not proof of a signature verifier.
The context is fixed; other business instances need their own effect proofs.
Infinite waiting is admitted; this proves safety, not fairness or liveness.
Human maintainer approval and Rust/model equivalence remain separate work.

The anuna-dev workflow influenced the work through spec-first obligations,
an executable Elephant dependency plan, cross-model review, and mutation testing.

## Elephant coordination

Store: `outputs/state-refinement-elephant`, theory `spec-019-state-rules`.
Theory ID: `5d8c4bfe41058bf55742e9cc4d3cb28b2f759d430a523353681a8366e1dc979f`.
The store uses one local steward identity; the independent reviewer is a session,
not a second signer. The identity private key is runtime material: do not commit
the store or its keys. The replayable plan contains no private material.

Proof completion receipt: `s-87b58e71ba1114c2`.
Checks completion receipt: `s-d6def43e3921bf96`.
Review completion receipt: `s-49adda24d7174575`.
All three promises are fulfilled; `next` returns no remaining tasks.
The aggregate completion derives through `r-refinement-complete`, not a manual aggregate assertion.
Closure fingerprint: `d33817bb25d0960bc7c953b543f4b6f4d6251ca783b2dd281ecddd829f531136`.
Final closure and derivation are saved in `state-refinement-elephant-completion.json`
and `state-refinement-elephant-fingerprint.json`.
