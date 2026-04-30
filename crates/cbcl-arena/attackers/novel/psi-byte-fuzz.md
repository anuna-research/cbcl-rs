# psi-byte-fuzz

## Short description

Emits a short non-UTF-8 byte sequence (`0xff 0xfe 0xfd 0xfc`) followed
by a truncated CBCL form (`(psi-salt :salt `). Designed to probe
whether the peer's UTF-8 decoder, S-expression parser, or causal
verifier mishandles partial / mixed-validity input. The expected
outcome is that the peer either rejects at UTF-8 decode (lossy decode
yields `U+FFFD` characters that no sub-form parses) or rejects at the
S-expression parse stage (truncated form with unmatched `(` and a
trailing keyword without value).

## Structural distinguishing features from `Malicious-published`

- `response-injection` (Malicious-published) uses pure-ASCII malformed
  CBCL. `byte-fuzz` is structurally distinct in two ways: (a) it begins
  with *invalid UTF-8 bytes*, exercising the byte-level decoder
  (handle_inbound's `core::str::from_utf8` step), not just the parser;
  (b) it mixes invalid-UTF-8 bytes with a separately-malformed CBCL
  fragment, so a peer that strips invalid bytes and re-parses might
  partially succeed.
- `quasi-protocol` (Malicious-novel) is fully valid UTF-8 + fully
  parsable + causally-invalid. `byte-fuzz` is the dual: byte-invalid
  + parse-invalid, attacking the earliest pipeline stages.
- All `Malicious-published` patterns produce well-formed UTF-8 bytes;
  none probe the byte-decode boundary.

## Originality declaration

To my knowledge as the implementer-author of this pattern, the
specific construction "non-UTF-8 prefix + truncated CBCL fragment"
designed to exercise both the byte-decode and parse stages of CON-1120
has not appeared in any public Arena game transcript prior to
SPEC-011's first commit. Live LLM Arena agents do not typically emit
non-UTF-8 byte sequences — they emit text — so this attack class is
specific to a deterministic-attacker library. The pattern targets a
defence boundary (byte-validity quarantine) that the CBCL discipline
covers but that NL-chat agents typically don't think about. — Hugo
O'Connor, 2026-04-30.
