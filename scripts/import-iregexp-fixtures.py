#!/usr/bin/env python3
"""Offline, deterministic adaptation of the pinned upstream fixtures. No CBCL calls."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent / "test-vectors/contracts/iregexp"
for source in json.loads((ROOT / "sources.json").read_text())["sources"]:
    assert hashlib.sha256((ROOT / source["file"]).read_bytes()).hexdigest() == source["sha256"], source

patterns = (ROOT / "upstream/cabo/simple.irl").read_text().splitlines()
syntax = [{"origin": f"cabo/simple.irl:{n}", "pattern": s[1:], "valid": s[0] != "-"}
          for n, s in enumerate(patterns, 1)]
# '*' marks known-broken example generation. Keep its syntax case, never its examples.
matching = []
entry = -1
for line in (ROOT / "upstream/cabo/simple.out").read_text().splitlines():
    if line and line[0] in "=-*":
        entry += 1
        assert line.startswith(patterns[entry]), (entry, line)
    elif line.startswith("                  ") and line.strip().startswith('"') and patterns[entry][0] == "=":
        for value in json.loads("[" + line.strip() + "]"):
            matching.append({"origin": f"cabo/simple.irl:{entry+1}", "pattern": patterns[entry][1:], "text": value, "matches": True})
assert entry + 1 == len(patterns)

# Exact selector allowlist: adapters project string inputs, not a JSONPath evaluator.
adapters = {
    "found match": ("a.*", "a", False), "double quotes": ("a.*", "a", False),
    "don't select match": ("a.*", "a", True), "not a match": ("a.*", "a", False),
    "select non-match": ("a.*", "a", True),
    "regex from the document": (None, None, False),
    "filter, match function, unicode char class, uppercase": (r"\p{Lu}", None, False),
    "filter, match function, unicode char class negated, uppercase": (r"\P{Lu}", None, False),
    "filter, match function, unicode, surrogate pair": ("a.b", None, False),
    r"dot matcher on \u2028": (".", None, False), r"dot matcher on \u2029": (".", None, False),
    "dot in character class": ("a[.b]c", None, False), "escaped dot": (r"a\.c", None, False),
    "escaped backslash before dot": (r"a\\.c", None, False),
    "escaped left square bracket": (r"a\[.c", None, False),
    "escaped right square bracket": (r"a[\].]c", None, False),
    "explicit caret": ("^ab.*", None, False), "explicit dollar": (".*bc$", None, False),
}
skipped = {"non-string first arg", "non-string second arg", "result cannot be compared", "too few params", "too many params", "arg is a function expression"}
for test in json.loads((ROOT / "upstream/jsonpath/match.json").read_text())["tests"]:
    name = test["name"]
    if name in skipped:
        continue
    pattern, field, invert = adapters[name]
    document = test["document"]
    if pattern is None:
        pattern = document["regex"]
        candidates = document["values"]
        prefix = "$['values']"
    else:
        candidates = document
        prefix = "$"
    # Check that the explicit mapping really names the pattern in the upstream selector.
    if name != "regex from the document":
        quoted = "'" + pattern.replace('\\', '\\\\').replace("'", "\\'") + "'"
        if name == "double quotes": quoted = json.dumps(pattern)
        assert quoted in test["selector"], (name, quoted, test["selector"])
    for i, candidate in enumerate(candidates):
        value = candidate.get(field) if field else candidate
        if not isinstance(value, str): continue
        selected = f"{prefix}[{i}]" in test["result_paths"]
        expected = not selected if invert else selected
        correction = name in {"explicit caret", "explicit dollar"}
        if correction: expected = False  # RFC 9485 grammar; upstream issue #122.
        row = {"origin": f"jsonpath/match.json:{name}[{i}]", "pattern": pattern, "text": value, "matches": expected}
        if correction: row["correction"] = "https://github.com/jsonpath-standard/jsonpath-compliance-test-suite/issues/122"
        matching.append(row)
output = json.dumps({"syntax": syntax, "matching": matching, "excluded_jsonpath_tests": sorted(skipped)}, ensure_ascii=True, indent=2) + "\n"
destination = ROOT / "upstream-cases.json"
if "--check" in sys.argv:
    assert destination.read_text() == output, "run scripts/import-iregexp-fixtures.py to refresh"
else:
    destination.write_text(output)
print(f"{len(syntax)} upstream syntax cases; {len(matching)} matching cases")
