#!/usr/bin/env bash
# Verify every CBCL artefact under demo/.
#
# - dialects/*.cbcl  → cbcl-cli verify (R1+R2+R3)
# - traces/*.scm     → cbcl-cli parse, one top-level form at a time
#
# Exits non-zero on the first failure; prints one summary line per file.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
DEMO="$ROOT/demo"
CLI=(cargo run -q -p cbcl-cli --)

cd "$ROOT"

fail=0

echo "== dialects (R1/R2/R3/R5 via cbcl-cli) =="
for f in "$DEMO"/dialects/*.cbcl; do
  [ -e "$f" ] || continue
  name="$(basename "$f")"
  if "${CLI[@]}" verify < "$f" >/dev/null 2>&1; then
    printf "  ok   %s\n" "$name"
  else
    printf "  FAIL %s\n" "$name"
    "${CLI[@]}" verify < "$f" || true
    fail=1
  fi
done

echo "== traces =="
for f in "$DEMO"/traces/*.scm; do
  [ -e "$f" ] || continue
  name="$(basename "$f")"
  # Strip comments and split into top-level S-expressions.
  # We use an awk-based depth counter so embedded newlines don't matter.
  bad=$(awk '
    BEGIN { depth = 0; buf = ""; idx = 0; bad = 0 }
    {
      sub(/;.*/, "")
      for (i = 1; i <= length($0); i++) {
        c = substr($0, i, 1)
        buf = buf c
        if (c == "(") depth++
        else if (c == ")") {
          depth--
          if (depth == 0) {
            idx++
            print idx "\t" buf
            buf = ""
          }
        }
      }
      buf = buf "\n"
    }
  ' "$f" | while IFS=$'\t' read -r idx form; do
    [ -z "${form// }" ] && continue
    if ! echo "$form" | "${CLI[@]}" parse >/dev/null 2>&1; then
      echo "$idx"
      break
    fi
  done)

  if [ -z "$bad" ]; then
    printf "  ok   %s\n" "$name"
  else
    printf "  FAIL %s (form #%s did not parse)\n" "$name" "$bad"
    fail=1
  fi
done

if [ "$fail" -ne 0 ]; then
  echo "FAILED" >&2
  exit 1
fi

echo "OK"
