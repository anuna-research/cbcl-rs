---
title: SPEC-035 implementation evidence
mode: reference
status: in-progress
---

# SPEC-035 Halo2 State Checkpoints — evidence record

Governing specification: `specs/SPEC-035-halo2-state-checkpoints.md`.
Generating model for the specification and orchestration: Claude Fable 5.1
(claude-fable-5-1), Claude Code 2.1.318, session 2026-11-04. Implementation
attempts run through Circus with `circus-driver-claude` (one-shot Claude Code);
each attempt's own evidence file is under `docs/evidence/circus/`.

## Specification review (TEST-3510, spec stage)

### Comprehension gate

A fresh-context agent (same model family, no access to the body) read only the
Orientation block of version 0.1.0 and answered: intent restated correctly;
case "unchecked signer label on both sides" predicted correctly (proof
verifies, authorship not guaranteed, REQ-3504 and the metaphor named); case
"chain gap" predicted correctly (REQ-3505, CON-3503); four deciding artefacts
named correctly. Fifteen ambiguities reported. Dispositions in 0.2.0: diagram
caption rewritten to match arrow directions; vocabulary paragraph defines
candidate vocabulary, native, enumeration, recognition, role-declaring dialect
and "admitted pair"; the `unauthenticated` consequence is stated (same profile
identity, proof silent on authorship); the metaphor now states that consequence;
REQ-3509 and REQ-3510 are integration conditions and stay out of Controls by
design; "Spindle Halo2 approach (user reference)" removed from prior art as
unsourced.

### Adversarial review

A fresh-context agent (same model family) reviewed version 0.1.0 against the
prototype code and upstream specs with a mandate to find defects. 26 findings:
3 critical, 9 major, 14 minor. Dispositions, numbered as reported:

| # | Finding | Disposition in 0.2.0 |
|---|---|---|
| 1 | `attested` required `Message::Simple` but candidates are `lang`-wrapped | Accepted. Attestation targets `innermost_simple()`; wrapper bound by REQ-3512 (b). ADR-3504 records it. |
| 2 | canonical key spelling `@ed25519:a` breaks literal `:from` equality | Accepted. Identity compared via `KeyId::parse`; label keeps `:from` text (REQ-3504 c, d). |
| 3 | `unauthenticated` as "only path" unenforceable with public fields | Accepted. Fields private, accessors added, `compile_fail` doctest in TEST-3503 (REQ-3504 a). |
| 4 | `Chain::verify` reads link statements, contradicting hard stop REQ-3502 | Accepted. REQ-3502 split (a)–(d); chain takes receiver start and optional expected end; ADR-3505 explains. |
| 5 | `Signer` carries no key identity; host can pair wrong key | Accepted as a boundary. Recorded as documented precondition in CON-3504, F2 narrowed to prover-side laundering, Open item added. |
| 6 | compile-time rejection contradicted existing test | Accepted. REQ-3512 keeps prototype behaviour: compile succeeds, sets invalid. |
| 7 | REQ-3509 vs REQ-3510 dependency contradiction | Accepted. REQ-3509 (b) names the `cbcl-cli` optional exception. |
| 8 | ABNF stricter/looser than `serde_json` | Accepted. CON-3502 restated as the recogniser's language with explicit whitespace, order, duplicate and integer rules. |
| 9 | thread and dialect binding tested but never required | Accepted. New REQ-3512, F7. |
| 10 | wrong anchor SPEC-019 CON-1908 | Accepted. Links to the SPEC-019 kernel section. |
| 11 | fuel 256 bounds nodes, not bytes | Accepted. REQ-3507 states the node budget and scope. |
| 12 | "absence of row allocation" undecidable; missing cases | Accepted. TEST-3506 uses `Err` plus a 100 ms bound and names new cases. |
| 13 | `Proof` lacks `PartialEq` | Accepted. REQ-3508 (c). |
| 14 | address spelling `sha256-<hex>` vs typed root | Accepted. CON-3500 and CON-3505 fix wire addresses. |
| 15 | limb order unspecified | Accepted. CON-3501 fixes limb 0 = bytes 0..16. |
| 16 | sort order is content address, not (label, canonical) | Accepted. CON-3500 corrected. |
| 17 | `SEMANTICS_VERSION` test is manual | Accepted. `relation_domain(version)` and a named test (REQ-3506 a, TEST-3505). |
| 18 | chain cannot start from trusted non-genesis | Accepted. Start parameter; `Profile::genesis` for the empty start. |
| 19 | `Prover` has no contract | Accepted. CON-3506. |
| 20 | multiple obligations per clause | Accepted. REQ-3502, 3504, 3506–3509 lettered; tests cite letters. |
| 21 | non-portable NFR; transcript overflow unruled | Accepted. NFR-3500 records machine; REQ-3508 (d) prove fails closed. |
| 22 | mutation configuration target "does not exist" | Partly accepted. `mutants.toml` exists at the repository root with an `examine_re` allow-list; REQ-3509 (d) now names it. |
| 23 | identity transition is a positive case; limb test maps to REQ-3500 | Accepted. TEST-3502 reworded and validates both. |
| 24 | whitespace test also covers CON-3500 post-conditions | Accepted as a note; test retained under TEST-3505 for identity invariance. |
| 25 | "notify the maintainer" and "own compiled profile" untestable | Accepted. REQ-3511 records open items in the evidence file; CON-3503 lists the precondition as unverifiable by the library. |
| 26 | `:from` string vs symbol spelling | Accepted. REQ-3512 states both are distinct candidates; golden vector pins the fixture spelling. |

Review tooling note: `usdd-count.sh` matches three-digit artefact ids and
undercounts this repository's four-digit ids; counts are therefore not pasted
here. `usdd-lint.sh` on 0.2.0: see the gate section below.

## Gates (filled by implementation tasks)

Pending.

## Mutations

Pending.

## Independent code review

Pending.

## Open items for the CBCL maintainer

Carried from the specification's Orientation; none closed by this record.
