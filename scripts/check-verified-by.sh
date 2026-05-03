#!/usr/bin/env bash
# REQ-517 / TEST-517: every REQ in SPEC-002 and SPEC-003 must carry a
# `verified-by:` annotation. Exits non-zero if any REQ block is missing one.
#
# Allowed values: lean | lean-with-sorry | property | example | prose | n/a
# (multiple values may appear comma-separated on a single line for partial
# mechanisation).
#
# Usage: scripts/check-verified-by.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

SPECS=(
    "$REPO_ROOT/specs/SPEC-002-structural-contracts.md"
    "$REPO_ROOT/specs/SPEC-003-verification-lattice.md"
)

ALLOWED_RE='^(lean|lean-with-sorry|lean \(soundness only\)|property|example|prose|n/a)$'

missing=0
bad_value=0

for spec in "${SPECS[@]}"; do
    if [[ ! -f "$spec" ]]; then
        echo "ERROR: spec not found: $spec" >&2
        exit 2
    fi

    # awk script: for each REQ-NNN heading, capture the block until the next
    # heading at the same level (### ) or a horizontal rule (---), and
    # require that the block contains a 'verified-by:' line whose value
    # matches the allowed set.
    awk -v spec="$spec" -v allowed="$ALLOWED_RE" '
        function flush(   line, val, parts, i, ok, v) {
            if (req_id == "") return
            if (verified == "") {
                printf("MISSING verified-by: %s line %d %s\n", spec, req_line, req_id) > "/dev/stderr"
                miss++
                return
            }
            # Strip "verified-by:" prefix and trim.
            line = verified
            sub(/^[[:space:]]*verified-by:[[:space:]]*/, "", line)
            sub(/[[:space:]]+$/, "", line)
            if (line == "") {
                printf("EMPTY verified-by value: %s line %d %s\n", spec, verified_line, req_id) > "/dev/stderr"
                bad++
                return
            }
            # Allow comma-separated values.
            n = split(line, parts, /[[:space:]]*,[[:space:]]*/)
            for (i = 1; i <= n; i++) {
                v = parts[i]
                if (v !~ allowed) {
                    printf("BAD verified-by value %s: %s line %d %s\n", v, spec, verified_line, req_id) > "/dev/stderr"
                    bad++
                }
            }
        }

        /^### REQ-[0-9]+/ {
            flush()
            req_id = $0
            req_line = NR
            verified = ""
            verified_line = 0
            in_req = 1
            next
        }

        /^### / || /^## / || /^---[[:space:]]*$/ {
            flush()
            req_id = ""
            in_req = 0
            next
        }

        in_req && /^verified-by:/ {
            verified = $0
            verified_line = NR
        }

        END {
            flush()
            if (miss > 0) printf("MISSING_COUNT %d\n", miss) > "/dev/stderr"
            if (bad > 0) printf("BAD_COUNT %d\n", bad) > "/dev/stderr"
            exit (miss > 0 || bad > 0) ? 1 : 0
        }
    ' "$spec" || {
        rc=$?
        if [[ $rc -ne 0 ]]; then
            missing=$((missing + 1))
        fi
    }
done

if [[ $missing -gt 0 ]]; then
    echo "FAIL: one or more REQs are missing or have invalid verified-by annotations." >&2
    exit 1
fi

echo "OK: every REQ in SPEC-002 and SPEC-003 has a valid verified-by annotation."
