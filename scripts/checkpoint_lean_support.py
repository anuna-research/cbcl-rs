"""Shared source, kernel-checking and semantic-diagnostic helpers for checkpoints."""
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean-cbcl"
MODULES = LEAN / "LeanCbcl"
RUST_ADAPTER = ROOT / "crates/cbcl-checkpoint/src/summary.rs"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def native_inventory(source):
    inventory = re.search(r"inductive Rule where(.*?)deriving DecidableEq", source, re.S)
    heads = re.search(r"def Rule.head : Rule → String(.*?)(?=/--|\ndef )", source, re.S)
    if not inventory or not heads:
        raise ValueError("missing full native rule/head inventory")
    names = re.findall(r"(?m)^\s*\|\s+(\w+)", inventory.group(1))
    pairs = re.findall(r'\|\s*\.(\w+)\s+\.\.\s*=>\s*"([^"\n]+)"', heads.group(1))
    residue = re.sub(r'\|\s*\.\w+\s+\.\.\s*=>\s*"[^"\n]+"', '', heads.group(1))
    if (residue.strip() or len(names) != 16 or len(set(names)) != 16
            or [name for name, _ in pairs] != names
            or len({head for _, head in pairs}) != 16):
        raise ValueError("full native sixteen-rule head inventory changed shape")
    return dict(pairs)


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def strip_noncode(text):
    """Ignore nested Lean comments and string literals; preserve line numbers."""
    out, i, block, string = [], 0, 0, False
    while i < len(text):
        if block:
            if text.startswith("/-", i): block += 1; out.extend("  "); i += 2
            elif text.startswith("-/", i): block -= 1; out.extend("  "); i += 2
            else: out.append("\n" if text[i] == "\n" else " "); i += 1
        elif string:
            if text[i] == "\\" and i + 1 < len(text): out.extend("  "); i += 2
            elif text[i] == '"': string = False; out.append(" "); i += 1
            else: out.append("\n" if text[i] == "\n" else " "); i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.extend(" " * (end - i)); i = end
        elif text.startswith("/-", i): block = 1; out.extend("  "); i += 2
        elif text[i] == '"': string = True; out.append(" "); i += 1
        else: out.append(text[i]); i += 1
    if block or string:
        raise ValueError("unterminated source comment/string")
    return "".join(out)


def bindings():
    paths = list(MODULES.rglob("*.lean")) + [RUST_ADAPTER]
    paths += [LEAN / x for x in ("LeanCbcl.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json") if (LEAN / x).is_file()]
    # Record precisely which compiled local imports trust-zero checking loads.
    paths += list((LEAN / ".lake/build/lib/lean/LeanCbcl").rglob("*.olean"))
    return {str(p.relative_to(ROOT)): sha(p) for p in sorted(paths)}


def run(command, timeout):
    started = time.monotonic()
    p = subprocess.Popen(command, cwd=str(LEAN), stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, text=True, encoding="utf-8",
                         errors="replace", start_new_session=True,
                         env=dict(os.environ, NO_COLOR="true"))
    timed_out = False
    try:
        try: stdout, stderr = p.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True; os.killpg(p.pid, signal.SIGKILL); stdout, stderr = p.communicate()
    except BaseException:
        if p.poll() is None: os.killpg(p.pid, signal.SIGKILL)
        p.wait(); raise
    return {"command": command, "cwd": str(LEAN), "exit_code": p.returncode,
            "timed_out": timed_out, "elapsed_seconds": round(time.monotonic() - started, 3),
            "stdout": stdout, "stderr": stderr}


def proof_rejection(result, source):
    code = strip_noncode(source)
    # Only errors inside named theorem declarations count. Definition/type/parser
    # failures by themselves do not establish that a theorem rejected semantics.
    declarations = list(re.finditer(r"(?m)^(?:@\[[^\n]+\]\s*)?(?:private\s+)?(theorem|def|structure|inductive|namespace|end)\b[^\n]*", code))
    ranges = []
    for i, d in enumerate(declarations):
        if d.group(1) == "theorem":
            start = code[:d.start()].count("\n") + 1
            end = code[:declarations[i+1].start()].count("\n") + 1 if i+1 < len(declarations) else len(code.splitlines())+1
            name = re.search(r"\btheorem\s+(\S+)", d.group()).group(1)
            ranges.append((start, end, name))
    output = result["stdout"] + result["stderr"]
    diagnostics = re.findall(r"(?m)^(.+?\.lean):(\d+):(\d+): error: ([^\n]+)", output)
    invalid = re.compile(r"unknown (?:module|constant|identifier|namespace)|object file|file not found|failed to import|unexpected token|expected token|unterminated|invalid character|unrecognized tactic", re.I)
    proof = re.compile(r"unsolved goals|type mismatch|tactic.*(?:failed|failure)|`(?:grind|simp)` failed|application type mismatch|failed to synthesize", re.I)
    errors = []
    bad = False
    for path, line, column, message in diagnostics:
        theorem = next((name for start,end,name in ranges if start <= int(line) < end), None)
        bad |= bool(invalid.search(message))
        if theorem and proof.search(message):
            errors.append({"theorem": theorem, "line": int(line), "column": int(column), "message": message})
    rejected = result["exit_code"] != 0 and not result["timed_out"] and bool(errors) and not bad
    return rejected, errors


def write_report(path, report):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", dir=str(path.parent), delete=False, prefix=".lean-proof-") as f:
        json.dump(report, f, indent=2); f.write("\n"); temporary = f.name
    os.replace(temporary, path)
