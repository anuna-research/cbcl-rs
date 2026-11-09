---
id: BUG-011
title: State root identity omits the sealed cast it interprets
severity: S2
priority: P1
status: in-progress
reported-date: 2026-11-09
assigned-to: SPEC-038 implementer and protocol maintainer
component: crates/cbcl-core/src/state.rs
---

# BUG-011: State root address does not bind immutable cast metadata

`Act::from_message` hashes the innermost simple message. Its identity validator
repeats that policy. Context casting reads the outer `with-roles` wrapper.
Changing only the reviewer roster therefore changes context metadata without
changing the state root address. Both variants are accepted into separate fresh
histories by the actual public state admission path.

This prevents deriving the fixed per-address metadata premise of the current
context proofs from native root identity. It is not a SHA-256 collision, nor
is the reproduction a universal SEC counterexample over equal complete `Act`
sets: the complete acts retain different outer messages. Host authentication
is an explicit premise of the API and was not cryptographically exercised.

The contracts conflict at the proposed repair:
[[SPEC-014-role-layer-endpoint-projection#REQ-625]] requires the root hash to
commit the whole `with-roles` wrapper, while
[[SPEC-038-lvar-state-kernel#REQ-3807]] preserves existing addresses.
This affects the native correspondence obligation for
[[SPEC-038-lvar-state-kernel#REQ-3811]] and
[[SPEC-038-lvar-state-kernel#TEST-3806]].

## Reproduced native behavior

Append this investigation to `crates/cbcl-parser/tests/state_context.rs`, using
that module's existing helpers:

```rust
#[test]
fn investigate_cast_address_binding() {
    let src = source(None);
    let d = parse_dialect(&parse(&src).unwrap()).unwrap();
    let first = root_act("");
    let second = act(r#"(with-roles ((chair @chair) (reviewer @x @y @z))
        (signed @chair (hello :thread "t" :caused-by begin)))"#, "@chair");
    assert_eq!(first.address, second.address);
    let thread = cbcl_core::store::ThreadId("t".into());
    for root in [&first, &second] {
        assert!(matches!(state_exports::admit(&d, &thread, &[], root),
            state_exports::Admission::Accepted));
    }
    let a = read(&src, &[first]);
    let b = read(&src, &[second]);
    assert_eq!(a["reviewers"], b["reviewers"]);
}
```

Run `cargo test -p cbcl-parser --test state_context
investigate_cast_address_binding -- --exact`. The final assertion fails:
`["@a","@b","@c"]` versus `["@x","@y","@z"]`. All preceding address and
admission assertions pass. The temporary investigation was removed after
capture; the production test suite is not left failing.

## Concrete repair proposal and compatibility evidence

`bugs/BUG-011-root-cast-identity-proposal.patch` is a review-only patch, not
applied production code. It is a zero-context review patch; validate applicability
with `git apply --unidiff-zero --check` before applying it. It hashes the outermost sealed wrapper for role roots,
updates both construction and identity validation, and adds a root commitment
regression. Nonroot and role-free hashing policies remain unchanged. Reissuing
messages with new root/predecessor references can change descendant addresses
and signatures even though the business-act hashing algorithm is unchanged.

The proposed patch was actually applied temporarily and tested, then completely
restored. All 15 context tests, including the proposed root commitment regression,
pass. The existing state corpus then fails its `bounded-ceiling` address vector:

- Current root: `sha256-6655c6fbcd385dd84414cad93d6cad9a1ed650f4c2834790d9043f543051d407`
- Proposed root: `sha256-00e5135405fae01e3135ee94a3a7e57f1f35fe19de5203d42462307db3585131`

The corpus stops at this first incompatibility; it does not prove the scope of
all migration effects. No vectors were rewritten to hide the failure. The patch
is a narrow mechanism prototype, not a completed migration implementation.

## Decision alternatives

Owner: protocol maintainer/user. The alternatives considered before the
recorded maintainer selection were:

1. Commit role-root identity to the sealed wrapper, explicitly authorize the
   address/predecessor migration, and amend the compatibility requirement.
2. Preserve addresses and add an explicit trusted immutable root-cast binding
   to the host/admission contract and corresponding interfaces/proofs.
3. Preserve addresses and extend kernel/store semantics to retain conflicting
   cast variants as fault evidence, including the accompanying witness and
   convergence obligations.

A same-store duplicate guard alone does not establish immutable metadata across
independently accepted branches. Independent read-only review confirmed this
mechanism and the compatibility conflict; it did not claim a general native
security or SEC theorem. Unrelated proof/implementation work may continue while
this identity contract is decided.

## Decision recorded — 2026-11-09

The maintainer explicitly selected hashing the sealed wrapper and migrating
addresses. [[SPEC-038-lvar-state-kernel#REQ-3807]] and
[[SPEC-038-lvar-state-kernel#ADR-3807]] record the amended compatibility contract.
The review-only patch remains a prototype until applied and verified; signed
history is not edited in place. Original historical baselines remain immutable,
and affected role-root cases require explicit reissue/mapping evidence.
Implementation and migration acceptance remain open.
