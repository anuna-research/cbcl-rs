# millionaire-protocol-mimicry

## Originality declaration

To the best of my knowledge, this attack pattern has not appeared in
public Arena game logs prior to SPEC-011's first commit (2026-04-30).
This declaration is signed by the author's git-attested commit message
per REQ-1131 (1).

## Design rationale

`protocol-mimicry` emits messages that look like CBCL bracket-protocol
messages — `(yao-bracket :round 0 :threshold 0 …)` — but with extra
keyword arguments that ask the peer to "quote your wealth in the
:commitment field". A naive CBCL-looking parser that strips unknown
keywords but echoes recognised ones can be coaxed into reflecting
content back from the request, e.g. by way of an over-eager templated
reply.

Against the `CbclAgent` reference, the dialect parser rejects
unrecognised keyword fields (R3 well-typed-content) and `verify_causal`
rejects the malformed `:caused-by` (R5), so the message is quarantined
and never affects state — which is exactly the property
`TEST-1130 (Yao subset, structural-rejection conformance)` verifies.

## Distinguishing features from `Malicious-published`

- **vs `direct-ask`:** dressed as a protocol message, not free-form
  prose.
- **vs `compare-by-naming`:** does not include an own-wealth reference.
- **vs `threshold-injection`:** numerical fields are real protocol
  fields (`:threshold 0`), not disguised payloads.
- **vs `social-pressure`:** no rapport framing.

The novelty axis is *syntactic mimicry*: hiding the disclosure prompt
inside dialect skin so it survives a credulous parser pipeline.
