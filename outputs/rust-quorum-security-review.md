# Independent Rust quorum security review

Reviewer: delegated fresh-context agent `/root/rust_quorum_security_review`, 2026-10-31.
Scope: [[SPEC-026-rust-quorum-certification]], [[SPEC-025-consensus-free-refinement]], Lean ConsensusFree/Core.lean, quorum runtime, certification configuration, parser, binder and R7 changes.

This was an adversarial code/model review, with independent executable probes. The parent records a requested reviewer model override of `gpt-6-astra`; this reviewer cannot independently verify runtime model identity or the producer model. No cross-model independence claim follows solely from that request. This is not formal extraction or human security approval.

## Finding and resolution

Programmatic committee configuration accepted validator names outside the parser symbol grammar. `Certification::quorum_budget(Some(vec!["@bad:key".into()]), None)` succeeded. The same gap covered brackets, backslashes and non-ASCII symbols, making programmatic/serde declarations disagree with language declarations. This violates [[SPEC-026-rust-quorum-certification#CON-2600]] and [[SPEC-026-rust-quorum-certification#TEST-2600]]. An independent rejection test executed and failed on `@bad:key`; the finding was sent immediately to the implementation agent. The implementation now uses the parser-compatible ASCII symbol character set and has programmatic/serde regression cases. No resource overspend exploit was established from this grammar defect.

## Safety review results

No remaining concrete safety blocker found in the inspected final implementation. The local budget multiplier matches the Lean charge bound. Costs are owner-local; mint/burn/pay/headroom operations preserve the model's resource interpretation. Self-transfers are refused. Operation certification alone never credits balances. Effects and cancellation fences exclude each other, while releases preserve signature and fence evidence. Complete sealed reports and own-journal inclusion protect checkpoint coverage; cumulative held/refunded/credited sets prevent duplicate refunds and repeated credits. New held entries must come from the parent epoch. One-successor choices and local parent installation prevent forked budget resets.

Certificates check domain, kind, payload, distinct committee members and signatures. Context identity commits the dialect, thread, root, opener, field and committee. A forged cached Instance.cast probe against the current implementation correctly failed authoring with `mint requires issuer authority`: issuer permissions are rebuilt from authenticated genesis. A duplicate-amount probe was rejected by the explicit resource-keyword recognizer.

Journal writes precede returned signing requests, with state rollback after CAS/storage failure. Idempotent retries only reproduce already durable decisions. Recovery replays semantic checks rather than trusting deserialization. The storage host's nonforking durable-log and authentication contracts remain essential assumptions.

Final views retain unknown completeness and require checkpoint credit evidence before dependent operations can be registered. No latest-balance or shared reservation service was introduced. Limits bound retained operations/checkpoints/events, signatures, report cardinality and operation bytes; host parsers/transport must bound allocation before constructing typed inputs.

## Evidence

`cargo test -p cbcl-parser --test quorum_runtime` passed during review. Independent temporary probes covered duplicate amount rejection, programmatic roster grammar rejection, and cached-cast issuer substitution. The temporary fixture was removed after communicating results because maintained regression coverage belongs in quorum_runtime.rs. No production files were edited by this reviewer.

Residual scope: deterministic test authentication is not production cryptography; physical durability, network decoding limits, extraction correctness, and human domain review remain integration/release obligations described by [[SPEC-026-rust-quorum-certification#CON-2601]].

## Final delta review

Reviewed the iterative candidate message preflight, proposal entrypoint validation before manifest hashing, strict proof serde recognition, nested JSON bounded-counter option conversion, and the final Instance cache reconstruction. The message preflight limits depth before recursive candidate identity rebuilding and authentication; it also bounds typed message work before canonical encoding. Wire decoders retain responsibility for allocation limits before constructing typed values. Context creation reconstructs public Instance caches from accepted acts and rejects distinct competing resource openers. Host authentication still supplies actual signatures and normal CBCL protocol admission.

The JSON adapter recognizes bounded nested arrays, symbols, keywords, handles and integers, then delegates option semantics to the same state-rule parser used by textual dialects. The existing contract byte limit bounds this conversion. Reserving escrow-nonce prevents caller declarations from taking compiler-owned bookkeeping. Independent probes verified rejection of duplicate fault options, duplicate validator identities, negative faults, unknown options, excess nesting and declared nonce fields. Omitted versus explicit host-gate JSON declarations produce identical canonical dialect hashes.

A second concrete finding was observed and repaired: unknown fields inside Manifest.allocation were ignored because nested Resources lacked deny_unknown_fields. The independent rejection test failed before correction and passed after the implementation added strict recognition to Resources. This was a recognition-policy gap, not an established overspend path.

Independent final probes all passed: nested resource unknown-field rejection; rejection of a seventy-layer message before a panic-on-use Authentication callback, with unchanged journal sequence; JSON semantics and closed-option checks. Their captured run is in `outputs/rust-quorum-security-delta-tests.log`. The temporary duplicated fixture was removed after review. The maintained quorum_runtime suite was rerun with serde enabled, including the final cache-forgery regression. No production files were edited by this reviewer.

Disposition: no unresolved review blocker found in the final inspected delta. The parent reports isolated guard mutation tests; this reviewer did not independently execute those mutations and does not use that report as independent mutation evidence. Physical durability, host admission, transport allocation limits, formal extraction and human domain review remain outside this review's executed scope.
