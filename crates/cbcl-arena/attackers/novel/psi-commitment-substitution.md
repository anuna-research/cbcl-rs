# psi-commitment-substitution (Malicious-novel)

## Originality declaration

This pattern is originally authored for SPEC-011 by the cbcl-rs implementer.
To the best of the implementer's knowledge, no pattern of this exact
structure has appeared in public Arena game logs prior to SPEC-011's first
commit. The implementer designed the pattern independently of any public
Arena transcript and has not consulted Arena game logs after the initial
design pass except (per REQ-1131.3) to verify originality.

## Description of the attack

The attacker emits a `psi-commit` set-commitment message early in the
handshake — but with a `:root` field whose digest does not correspond to
any sorted-Merkle-root of the elements the attacker would later reveal.
The attacker then emits a `psi-reveal` whose hash list is a permutation of
the salt-hashes of *the peer's expected universe* (e.g. fabricated entries
that the attacker guesses might be in the peer's set), not of any set the
attacker actually holds.

The intent: the peer accepts the commitment, then later receives a reveal
whose digests collide with members of its own set. If the peer trusts the
overlap as evidence of intersection, it will name those elements in
`psi-claim` — leaking own-set members that are not actually in the true
intersection (since the attacker never had a real set).

## Why CBCL's discipline rejects it

The attacker's `psi-commit` and `psi-reveal` arrive *without* a valid
`:caused-by` chain rooted at a `psi-salt` the peer has accepted: the
attacker did not run the salt-exchange phase honestly. The peer's
`verify_causal` against the dialect's `(then begin psi-salt psi-commit
psi-reveal psi-claim psi-final)` protocol returns `Violation` (commit
references a non-`psi-salt` predecessor) or `Unknown` (the cited salt-hash
is not in the peer's store). Either result quarantines the message.

Even if the attacker fabricated a syntactically-plausible salt thread, the
peer's PSI strategy keys its intersection computation off the hash-overlap
between *its own* sorted-digest list (built from its own salted set) and
the *peer's* reveal-list. A substituted commitment cannot retro-coerce the
peer's own digest list, and the peer's claim is derived from its own
private set — not from anything the attacker said. So the leakage path the
attack relies on (peer parrots back attacker-suggested intersection
members) is closed by the strategy's hash-equality check, which is in turn
closed by the dialect's commitment-then-reveal ordering.
