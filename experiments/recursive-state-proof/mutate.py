#!/usr/bin/env python3
"""Check arithmetic negative tests against deliberate circuit faults."""
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
source = ROOT/'program.ts'
original = source.read_text()
mutants = [
    ('unbound-parent', "context.left.assertEquals(previous.publicOutput.root, 'unexpected predecessor');", '// MUTATION: parent root left unbound.', 'append public parent root binding'),
    ('dropped-right-input', 'assertSubset(object, b, union);', '// MUTATION: permit dropping the right input.', 'merge omitted right contribution'),
]
results = []
try:
    for name, target, replacement, test in mutants:
        assert original.count(target) == 1
        source.write_text(original.replace(target, replacement))
        run = subprocess.run(['node','--import','tsx','experiment.ts','--constraints-only'],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120)
        (ROOT/'evidence'/f'mutant-{name}.log').write_text(run.stdout.rstrip()+'\n')
        killed = run.returncode != 0 and 'Missing expected rejection' in run.stdout and test in run.stdout
        results.append({'mutant':name,'test':test,'exit_code':run.returncode,'killed':killed})
        print(json.dumps(results[-1]),flush=True)
finally:
    source.write_text(original)
(ROOT/'evidence/mutations.json').write_text(json.dumps(results,indent=2)+'\n')
sys.exit(0 if len(results)==len(mutants) and all(r['killed'] for r in results) else 1)
