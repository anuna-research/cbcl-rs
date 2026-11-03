# CBCL IETF Internet-Draft

This directory contains the IETF Internet-Draft specification for CBCL (Common
Business Communication Language).

The draft is the **normative prose specification** of the language. Its ABNF is
derived from the reference implementation in `crates/`, not from the LangSec
paper; where the two disagree, the implementation is the source of truth and the
divergence is recorded in the draft's "Divergences from this specification"
appendix (which the RFC Editor removes before publication).

## Files

- **draft-oconnor-cbcl.md** — source markdown (edit this)
- **draft-oconnor-cbcl.xml** — generated XML (RFC 7991 format)
- **draft-oconnor-cbcl.txt** — generated text format (for IETF submission)
- **draft-oconnor-cbcl.html** — generated HTML (for web viewing)
- **generate-rfc.sh** — build script to regenerate outputs
- **Makefile** — same, via `make`

`draft-cbcl.{xml,txt,html,pdf}` are stale outputs of a source file that no
longer exists (the draft was renamed to the IETF individual-submission
convention `draft-<surname>-<name>`). They can be deleted.

## Prerequisites

```bash
gem install kramdown-rfc     # Ruby; installs to ~/.gem/ruby/<ver>/bin
pip install xml2rfc          # Python
pip install weasyprint       # optional, for PDF
```

If `kramdown-rfc` is not on `PATH`, add the gem bin directory:

```bash
export PATH="$HOME/.gem/ruby/$(ruby -e 'print RUBY_VERSION.sub(/\d+$/, "0")')/bin:$PATH"
```

## Building

```bash
make            # build all formats
make clean      # remove generated files
make help       # show available targets
```

or `./generate-rfc.sh`, or manually:

```bash
kramdown-rfc draft-oconnor-cbcl.md > draft-oconnor-cbcl.xml
xml2rfc draft-oconnor-cbcl.xml --text --html
```

The draft stem is defined once, as `DRAFT` at the top of the `Makefile` and
`DRAFT_NAME` in `generate-rfc.sh`.

## Editing

The source uses kramdown-rfc markdown with YAML frontmatter.

Structure:

- Frontmatter: metadata, authors, normative and informative references
- Abstract, Introduction, Layering, Terminology
- **Core**: message format (three ABNF layers), dialect extension, R1–R4
- **Contracts**: causal protocols, shape constraints, R5, verification verdicts
- **Roles**: role annotations, casts, R6, endpoint projection, splicing boundary
- Content addressing, attestation disciplines, redacted envelopes
- Core semantics, conformance, security considerations, IANA registration
- Back matter: acknowledgments, implementation status, divergences, rationale

### Keeping the draft honest

Two rules, learned the hard way:

1. **Every example must be executed, not just written.** Message examples go
   through `cbcl-cli parse`; dialect definitions through `cbcl-cli verify`;
   role-bearing dialects through `cbcl_core::r6::r6_violations`; expansion
   examples through `cbcl_core::template::expand_template` with the expected
   output asserted verbatim. Earlier revisions carried a headline example using
   an `&key` marker that cannot be lexed at all, and an expansion that the
   expander does not produce.
2. **Anchors must be unique.** `xml2rfc` fails on a duplicate `anchor`, and the
   error names the second use, not the collision.

Note that `cbcl-cli verify` covers R1, R2, R3 and R5 only — it does **not** run
the R6 role checks, so role-bearing examples need the library call.

## Submission

1. Review `draft-oconnor-cbcl.txt`
2. Visit https://datatracker.ietf.org/submit/
3. Upload the `.txt` (or the `.xml`)

## Resources

- [IETF Internet-Draft Guidelines](https://ietf.github.io/id-guidelines/)
- [kramdown-rfc](https://github.com/cabo/kramdown-rfc)
- [xml2rfc](https://xml2rfc.tools.ietf.org/)
- [RFC 7991 — xml2rfc v3 Vocabulary](https://www.rfc-editor.org/rfc/rfc7991.html)

## Version History

- **draft-oconnor-cbcl-01** (2026-08-13): brought in line with the reference
    implementation based on `febc669`, with mandatory `lang` scoping added.
  - Renamed from `draft-cbcl` to the individual-submission convention; the
    build scripts now derive every filename from one stem variable
  - ABNF rewritten from `crates/cbcl-parser/src/parser.rs` and
    `crates/cbcl-core/src/message.rs`: custom performatives require an enclosing
    `lang` wrapper, multicast recipient sets, reserved `:thread`/`:sender`/`:caused-by`
    parameters, the `with-roles` wrapper, and explicit tokenization rules
  - Corrected R2 system limits to depth ≤ 64, expansion ≤ 8192, verification
    ≤ 1000 ms (previously stated as ≤ 32 and ≤ 5000 ms), and documented the
    defaults that apply when the clause is omitted
  - Removed the `&key` parameter marker and the `(or a b)` template form:
    neither exists, and `&` is outside the symbol alphabet. Documented the
    real template language (`literal`, `cond`, sequences, plain substitution),
    including that special forms are recognized only in head position
  - New sections: message contracts and R5, the multiparty role layer and R6,
    endpoint projection and the splicing boundary, content addressing with
    typed Merkle roots and field openings, attestation disciplines v1/v2/v3,
    redacted envelopes, equivocation, three-valued verification verdicts
  - New conformance section defining Core / Contracts / Roles levels, and
    requiring exactly one S-expression recognizer per implementation
  - Security considerations extended: scope of the guarantee, parser
    uniqueness, privacy properties of envelopes and field openings
  - Added a divergences appendix recording where the reference implementation
    does not yet match this specification (see `bugs/BUG-005`, `bugs/BUG-006`)
- **draft-cbcl-00** (2025-10-27): initial version
  - Core message format and grammar
  - Dialect extension mechanism
  - Security considerations (unbounded attack surface analysis)
  - IANA media type registration for `application/cbcl`
