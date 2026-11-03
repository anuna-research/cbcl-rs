#!/usr/bin/env python3
"""Regenerate the shared fixture with Lean's executable, kernel-checked oracle.

Use --write only when intentionally updating the reference fixture. Normal mode
compares structural JSON and fails if checked-in vectors drift from Lean.
"""
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
run = subprocess.run(['lake','env','lean','--run','MultiParentRustOracle.lean'],
                     cwd=ROOT/'lean-cbcl',capture_output=True,text=True,timeout=120,check=True)
reference = json.loads(run.stdout.splitlines()[-1])
file = ROOT/'test-vectors/quorum/multi-parent-lean.json'
if '--write' in sys.argv:
    file.write_text(json.dumps(reference,separators=(',',':'))+'\n')
else:
    if json.loads(file.read_text()) != reference:
        raise SystemExit('Shared Rust fixture differs from Lean oracle; inspect before --write')
print(json.dumps({'oracle':'MultiParentRustOracle.lean','traces':len(reference['traces']),
    'commands':sum(len(t['steps']) for t in reference['traces']), 'matches':True}))
