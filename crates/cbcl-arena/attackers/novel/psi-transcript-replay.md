# psi-transcript-replay (Malicious-novel)

## Originality declaration

This pattern is originally authored for SPEC-011 by the cbcl-rs implementer.
To the best of the implementer's knowledge, no pattern of this exact
structure has appeared in public Arena game logs prior to SPEC-011's first
commit. Designed independently of any public Arena transcript.

## Description of the attack

The attacker replays a verbatim transcript captured (or fabricated as
captured) from a *different* PSI game between two other agents. Each
replayed message is well-formed CBCL — performative, content,
`:caused-by` digests, `:thread`, `:sender` — and was honest in its
original game. The attacker's hope is that a peer with a permissive
parser/store will accept these messages as part of the current game and
fold the replayed plaintexts into its own intersection computation.

The intended damage: if the replayed `psi-claim` names plaintexts that
happen to overlap with the peer's private set, the peer's confirmation of
those plaintexts via its own `psi-final` would constitute a leak (those
items are in the peer's set but not the true intersection of the *current*
game).

## Why CBCL's discipline rejects it

CBCL's `:thread` field binds messages to a per-game thread root. The
honest peer's `MessageStore` is scoped by `ThreadId`, and `verify_causal`
runs against a thread-local view of the store. Replayed messages from a
prior game carry a different `:thread` value, so their `:caused-by`
digests do not resolve in the current peer's store, returning
`VerificationResult::Unknown`. The peer's CBCL agent quarantines the
replayed traffic.

Even within a single thread, every `:caused-by` references a
content-hashed predecessor; an attacker cannot synthesise a chain rooted
at the *current* peer's `psi-salt` digest unless the peer first emits
that `psi-salt` — and even then the replayed `psi-commit`/`psi-reveal`
hashes are the *original* attacker-pair's hashes, not derivable from the
peer's salt. The chain breaks at the first replayed edge.
