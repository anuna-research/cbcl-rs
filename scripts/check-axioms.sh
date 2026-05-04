#!/usr/bin/env bash
# NFR-511 / TEST-551 / OBS-512: axiom-discipline check.
#
# Runs `lake env lean AxiomAudit.lean` in `lean-cbcl/`, parses the
# `'<thm>' depends on axioms: [...]` lines emitted by `#print axioms`,
# and asserts only allowlisted axioms appear.
#
# Allowlist (kept in sync with the header comment in AxiomAudit.lean
# and with NFR-511 + ADR-515 in specs/SPEC-005-lean-mechanisation.md):
#
#   * propext, Classical.choice, Quot.sound — the standard Lean kernel
#     axioms permitted by NFR-511 clause 1.
#   * CBCL.ContentHash, CBCL.ContentHash.instNonempty, CBCL.contentHash,
#     CBCL.contentHash_injective, CBCL.Message.causedBy — the project
#     axioms enumerated by ADR-515 (cryptographic-hash carrier +
#     injectivity, and the opaque `:caused-by` accessor on the abstract
#     Message type). NFR-511 clause 2 admits *only* this set; adding any
#     further project axiom requires an ADR amendment, not just an
#     allowlist edit.
#
# Any axiom outside this allowlist is a build-fail (e.g. an accidental
# `axiom foo : True` introduced during proof development).
#
# Exit codes:
#   0 — clean: every theorem audited, every axiom allowlisted.
#   1 — non-allowlisted axiom found, or theorem count mismatch.
#   2 — lean failed to compile AxiomAudit.lean (typo, missing import).
#
# Usage: scripts/check-axioms.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
LEAN_DIR="$REPO_ROOT/lean-cbcl"
AUDIT_FILE="$LEAN_DIR/AxiomAudit.lean"

if [[ ! -f "$AUDIT_FILE" ]]; then
    echo "ERROR: $AUDIT_FILE not found." >&2
    exit 2
fi

ALLOWED_AXIOMS=(
    propext
    Classical.choice
    Quot.sound
    CBCL.ContentHash
    CBCL.ContentHash.instNonempty
    CBCL.contentHash
    CBCL.contentHash_injective
    CBCL.Message.causedBy
)

is_allowed() {
    local axiom="$1"
    local allowed
    for allowed in "${ALLOWED_AXIOMS[@]}"; do
        if [[ "$axiom" == "$allowed" ]]; then
            return 0
        fi
    done
    return 1
}

cd "$LEAN_DIR"

raw_output="$(mktemp)"
trap 'rm -f "$raw_output"' EXIT

if ! lake env lean AxiomAudit.lean > "$raw_output" 2>&1; then
    echo "ERROR: lake env lean failed on AxiomAudit.lean:" >&2
    sed 's/^/    /' "$raw_output" >&2
    exit 2
fi

# Any line containing "error" indicates a missing theorem, typo, or
# similar — we want loud failure rather than a silent pass with
# fewer-than-expected theorems audited.
if grep -Eq '^[^:]*:[0-9]+:[0-9]+: error' "$raw_output"; then
    echo "ERROR: AxiomAudit.lean produced compile errors:" >&2
    sed 's/^/    /' "$raw_output" >&2
    exit 2
fi

# Collapse continuation lines (Lean wraps long axiom lists) so each
# `'thm' depends on axioms: [...]` block is a single line.
collapsed="$(awk '
    /^'\''[^'\'']+'\''/ {
        if (NR > 1) print buf;
        buf = $0;
        next
    }
    {
        # continuation: strip leading whitespace and append.
        sub(/^[[:space:]]+/, "");
        buf = buf " " $0;
    }
    END { if (buf != "") print buf }
' "$raw_output")"

expected_count="$(grep -c '^#print axioms ' AxiomAudit.lean)"
actual_count="$(printf '%s\n' "$collapsed" | grep -c "^'" || true)"

if [[ "$expected_count" -ne "$actual_count" ]]; then
    echo "ERROR: expected $expected_count theorems audited, got $actual_count." >&2
    echo "Audit output:" >&2
    printf '%s\n' "$collapsed" | sed 's/^/    /' >&2
    exit 1
fi

bad=0
audited=0
while IFS= read -r line; do
    [[ -z "$line" ]] && continue

    thm="$(printf '%s\n' "$line" | sed -E "s/^'([^']+)'.*/\1/")"
    audited=$((audited + 1))

    if [[ "$line" == *"does not depend on any axioms"* ]]; then
        continue
    fi

    # Extract the comma-separated axiom list from `[ ... ]`.
    list="$(printf '%s\n' "$line" | sed -E 's/.*\[(.*)\].*/\1/')"
    if [[ "$list" == "$line" ]]; then
        echo "ERROR: could not parse axiom list for $thm: $line" >&2
        bad=$((bad + 1))
        continue
    fi

    IFS=',' read -ra axioms <<< "$list"
    for axiom in "${axioms[@]}"; do
        # Trim whitespace.
        axiom="${axiom#"${axiom%%[![:space:]]*}"}"
        axiom="${axiom%"${axiom##*[![:space:]]}"}"
        [[ -z "$axiom" ]] && continue

        if ! is_allowed "$axiom"; then
            echo "FAIL: $thm depends on non-allowlisted axiom: $axiom" >&2
            bad=$((bad + 1))
        fi
    done
done <<< "$collapsed"

if [[ "$bad" -gt 0 ]]; then
    echo "" >&2
    echo "FAIL: $bad non-allowlisted axiom dependency(ies) found across $audited theorem(s)." >&2
    echo "If a new axiom is intentional, add it to ALLOWED_AXIOMS in this script and" >&2
    echo "to the header comment in lean-cbcl/AxiomAudit.lean, with justification." >&2
    exit 1
fi

echo "OK: $audited theorem(s) audited; all axioms allowlisted."
