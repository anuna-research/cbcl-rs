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

The motivating data point: `arena.nicolaos.org` (Greco et al., 2026)
publicly lists a top PSI attacker — `Malicious (claude-sonnet-4-6)` —
reaching a 43% success rate against the leaderboard's "Unbeaten"
agents at 2026-04-30. The arena's inter-agent channel is unstructured
NL chat. Whatever the specific attack mechanism (the arena reports
rates, not transcripts), the channel admits a wide class of probe
shapes — extraction prompts, role-play impersonation, payload
smuggling, out-of-order assertions — that a free-form-chat agent's
strategy LLM has to defend against in prose.

`cbcl-arena` is a separate deterministic simulator we stand up to
exercise that defence claim directly. It re-implements the four
arena games (PSI, Yao, DC, Auction, plus Ultimatum) with controlled
threat models, an author-crafted attacker library (Malicious-published
+ Malicious-novel categories), and a vanilla NL-chat comparator that
calibrates to within statistical confidence of the arena's 43%
baseline. CBCL's contribution is structural: replacing the chat
channel with CBCL deletes the injection surface — malformed messages
fail at the parser; well-formed but out-of-order messages fail at
`verify_causal` returning `Violation`; nothing reaches the strategy
layer that wasn't both syntactically and causally valid. The
deterministic simulator measures this property directly against
controlled inputs rather than indirectly through arena leaderboard
rates.

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
