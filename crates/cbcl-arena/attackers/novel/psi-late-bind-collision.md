# psi-late-bind-collision (Malicious-novel)

## Originality declaration

This pattern is originally authored for SPEC-011 by the cbcl-rs implementer.
To the best of the implementer's knowledge, no pattern of this exact
structure has appeared in public Arena game logs prior to SPEC-011's first
commit. Designed independently of any public Arena transcript.

## Description of the attack

The attacker waits until *after* the peer has emitted `psi-reveal`, then
re-emits its own `psi-salt` carrying a different salt value than the one
the peer originally observed. The intent is to "late-bind" a new common
salt that, when applied to the peer's already-revealed digest list, would
allow the attacker to enumerate candidate plaintexts (an offline
dictionary attack against the peer's set across the universe).

A naive peer that recomputes its common-salt on every received `psi-salt`
would re-derive its digests under the new salt and re-emit them, leaking
its full set under two distinct salts. With two salts the attacker can
intersect candidate-plaintext lists and concentrate guesses on items in
the peer's set.

## Why CBCL's discipline rejects it

The dialect's protocol clause is a *single-pass* causal chain:
`begin → psi-salt → psi-commit → psi-reveal → psi-claim → psi-final`. By
the time the peer has sent `psi-reveal`, the peer's local state machine
has consumed the `psi-salt` predecessor and committed to the salt value.
A second `psi-salt` from the attacker arrives with `:caused-by begin`
(violating uniqueness — the protocol DAG admits exactly one `psi-salt`
event per thread) or with `:caused-by` pointing at something other than
the begin sentinel (violating the dialect's `then begin psi-salt …` edge).
`verify_causal` returns `Violation` and the message is quarantined.

The strategy in `agents/cbcl/psi.rs` further refuses to overwrite
`peer_salt` once set (`if self.peer_salt.is_some() { return; }`), so even
were the discipline bypassed, the strategy would not re-derive its
digests under a fresh salt.
