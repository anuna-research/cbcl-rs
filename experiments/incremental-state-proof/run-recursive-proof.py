#!/usr/bin/env python3
"""Run one real recursive incremental-history experiment with explicit local resource caps."""
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / 'evidence/recursive'
EVIDENCE.mkdir(exist_ok=True)
log = EVIDENCE / 'real-proof-run.log'
started = time.monotonic()
peak_rss = 0
minimum_free = shutil.disk_usage(ROOT).free
reason = None

def tree_rss(pid):
    rows = subprocess.check_output(['ps', '-axo', 'pid=,ppid=,rss='], text=True).splitlines()
    entries = [tuple(map(int, row.split())) for row in rows if len(row.split()) == 3]
    pids = {pid}
    while True:
        expanded = pids | {p for p, parent, _ in entries if parent in pids}
        if expanded == pids:
            break
        pids = expanded
    return sum(rss * 1024 for p, _, rss in entries if p in pids)

with log.open('w') as output:
    child = subprocess.Popen(['node', '--import', 'tsx', 'recursive-prove.ts', *sys.argv[1:]], cwd=ROOT,
                             stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
    print(json.dumps({'pid': child.pid, 'status': 'started', 'rss_cap_bytes': 4*1024**3}), flush=True)
    position = 0
    try:
        while child.poll() is None:
            time.sleep(2)
            text = log.read_text()
            if len(text) > position:
                print(text[position:], end='', flush=True)
                position = len(text)
            rss = tree_rss(child.pid)
            peak_rss = max(peak_rss, rss)
            free = shutil.disk_usage(ROOT).free
            minimum_free = min(minimum_free, free)
            if rss > 4*1024**3:
                reason = 'RSS cap exceeded'
            elif free < 1024**3:
                reason = 'disk reserve crossed'
            elif time.monotonic()-started > 30*60:
                reason = '30 minute run limit exceeded'
            if reason:
                os.killpg(child.pid, signal.SIGTERM)
                try:
                    child.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    os.killpg(child.pid, signal.SIGKILL)
                break
    finally:
        if child.poll() is None:
            os.killpg(child.pid, signal.SIGTERM)
        code = child.wait()
    text = log.read_text()
    if len(text) > position:
        print(text[position:], end='', flush=True)
result = {'exit_code': code, 'limit_reason': reason, 'seconds': round(time.monotonic()-started, 2),
          'peak_observed_tree_rss_bytes': peak_rss, 'minimum_observed_free_bytes': minimum_free}
(EVIDENCE/'run-status.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result), flush=True)
sys.exit(0 if code == 0 and reason is None else 1)
