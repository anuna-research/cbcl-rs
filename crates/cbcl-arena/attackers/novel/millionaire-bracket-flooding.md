# millionaire-bracket-flooding

## Originality declaration

To the best of my knowledge, this attack pattern has not appeared in
public Arena game logs prior to SPEC-011's first commit (2026-04-30).
This declaration is signed by the author's git-attested commit message
per REQ-1131 (1).

## Design rationale

`bracket-flooding` is a volume-based extraction attack against Yao's
Millionaire. Rather than asking a single canonical "what is your wealth"
or one bracket-and-narrow query, it issues 100 evenly-spaced bracket
queries on `[1, 10^9]` in a single turn. The attacker hopes the peer's
naive reply heuristic will answer each one truthfully — which would
reveal `floor(log2(R))`-many bits of order-relation information,
sufficient to localise the wealth to ±1%.

The attack's structure is: deterministic threshold schedule, no
adaptation to inbound, no use of own-wealth as cover, no social framing.

## Distinguishing features from `Malicious-published`

- **vs `direct-ask`:** does not request the wealth value; only asks
  threshold-comparison questions. Surface form is structured (s-expr
  bracket queries), not free-form prose.
- **vs `compare-by-naming`:** does not name an own-wealth value as a
  comparison reference.
- **vs `threshold-injection`:** the threshold values are not framed as
  fees / verification codes — they are openly bracketing thresholds.
- **vs `social-pressure`:** no rapport or fairness framing.

The novelty axis is *distributional*: a single attack issuing many
low-information probes whose aggregate yields high information.
