# Arena × CBCL demo

Four custom CBCL dialects, one per challenge on
[arena.nicolaos.org](https://arena.nicolaos.org/challenges):

| Challenge | Dialect | Trace(s) |
|---|---|---|
| Private Set Intersection | [`dialects/psi.cbcl`](dialects/psi.cbcl) | [honest](traces/psi-honest.scm), [adversarial](traces/psi-adversarial.scm) |
| Yao's Millionaire | [`dialects/millionaire.cbcl`](dialects/millionaire.cbcl) | [honest](traces/millionaire-honest.scm), [adversarial](traces/millionaire-adversarial.scm) |
| Dining Cryptographers | [`dialects/dining.cbcl`](dialects/dining.cbcl) | [honest](traces/dining-honest.scm) |
| Ultimatum Game | [`dialects/ultimatum.cbcl`](dialects/ultimatum.cbcl) | [honest](traces/ultimatum-honest.scm) |

Each dialect:

- Verifies under R1 (no recursion), R2 (resource bounds), R3 (no core
  redefinition) via `cbcl-cli verify`.
- Embeds a `(protocol (then ...)+)` clause declaring the legal causal
  sequence of messages, statically checked by R5 (acyclicity,
  reachability, definedness, uniqueness — see
  `crates/cbcl-core/src/protocol.rs`).

## Why

The arena's inter-agent chat is plain text, and the current top
attacker on PSI (`Malicious (claude-sonnet-4-6)`, 43% success rate) wins
by social engineering the opponent's strategy LLM. Replacing that
channel with CBCL deletes the entire injection surface: malformed
messages fail at the parser; well-formed but out-of-order messages
fail at `verify_causal` returning `Violation`; nothing reaches the
strategy layer that wasn't both syntactically and causally valid.

The cryptography (commit/reveal, DC-net XOR, etc.) is unchanged from
the textbook protocols. CBCL's contribution is making the channel
typed and the sequencing inspectable rather than implicit.

## Verify

```bash
bash demo/verify.sh
```

Verifies every dialect and parses every trace message-by-message.
Exits non-zero on any failure.

## Out of scope

- The live REST adapter (`cbcl-arena` shell crate) — tracked in
  [`plans/EXPLORE-arena.spl`](../plans/EXPLORE-arena.spl).
- Real cryptographic primitives — traces use placeholder hex digests
  to keep the focus on the protocol grammar.
- Networked play against live opponents.

## See also

- [`plans/IMPL-arena-demo.spl`](../plans/IMPL-arena-demo.spl) — task plan for this demo.
- [`plans/EXPLORE-arena.spl`](../plans/EXPLORE-arena.spl) — broader strategy.
