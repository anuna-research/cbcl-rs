#!/usr/bin/env python3
"""Bound offline app-format benchmarks; never contacts a running app."""
import json
import os
from pathlib import Path
import subprocess
import time

os.chdir(Path(__file__).resolve().parent)
out = Path('evidence/benchmark')
out.mkdir(parents=True, exist_ok=True)
for count in (128, 1024, 4096):
    for points in (4, 30):
        (out / f'drawing-{count}-{points}.json').unlink(missing_ok=True)
        (out / f'drawing-{count}-{points}-run.json').unlink(missing_ok=True)
        start = time.monotonic()
        with (out / f'drawing-{count}-{points}.log').open('w') as log:
            try:
                run = subprocess.run(['node', 'drawing-benchmark.mjs', str(count), str(points)], stdout=log, stderr=subprocess.STDOUT, timeout=300, check=False)
                result = {'operations': count, 'points': points, 'exit': run.returncode, 'seconds': time.monotonic() - start}
            except subprocess.TimeoutExpired:
                result = {'operations': count, 'points': points, 'status': 'timeout', 'seconds': time.monotonic() - start}
        (out / f'drawing-{count}-{points}-run.json').write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps(result), flush=True)
        if result.get('exit') != 0:
            raise SystemExit('Drawing benchmark failed or exceeded five minutes; inspect log.')
