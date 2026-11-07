#!/usr/bin/env python3
"""Real SIGTERM/process-group smoke; no browser, Cargo or proof workload.

Usage: python3 experiments/private-vote-export/browser/check-manager.py
Durable evidence goes under outputs/jolt-dory-browser/manager-smoke-<unique>/.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import uuid

# The managed child deliberately creates a separate session, as Chrome/CDP do.
# It reaps that child when the manager signals both groups, avoiding zombie-only
# false positives in the assertion that each entire group has disappeared.
CHILD = r'''
import json, os, pathlib, signal, subprocess, sys, time
pidfile = pathlib.Path(sys.argv[1])
sleeper = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'], start_new_session=True)
def stop(_signal, _frame):
    try:
        sleeper.wait(timeout=1.5)
    except subprocess.TimeoutExpired:
        # Do not repair the manager's detached-group cleanup: the smoke must fail.
        pass
    raise SystemExit(23)
signal.signal(signal.SIGTERM, stop)
value = {'child_pid': os.getpid(), 'child_pgid': os.getpgrp(), 'detached_pid': sleeper.pid, 'detached_pgid': os.getpgid(sleeper.pid)}
tmp = pidfile.with_suffix('.tmp')
tmp.write_text(json.dumps(value))
os.replace(tmp, pidfile)
while True:
    time.sleep(1)
'''


def group_exists(pgid):
    try:
        os.killpg(pgid, 0)
        return True
    except ProcessLookupError:
        return False


def discovered_groups(manager_pid):
    # Cleanup-only discovery covers failures before the PID handshake arrives.
    rows = subprocess.check_output(['ps', '-axo', 'pid=,ppid=,pgid='], text=True, timeout=1)
    parsed = [tuple(map(int, line.split())) for line in rows.splitlines() if len(line.split()) == 3]
    ids = {manager_pid}
    while True:
        expanded = ids | {pid for pid, ppid, _ in parsed if ppid in ids}
        if expanded == ids:
            break
        ids = expanded
    return {pgid for pid, _, pgid in parsed if pid in ids}


def main():
    root = Path(__file__).resolve().parents[3]
    output = root / 'outputs/jolt-dory-browser' / ('manager-smoke-' + uuid.uuid4().hex[:12])
    output.mkdir(parents=True, exist_ok=False)
    pidfile = output / 'pids.json'
    manager = None
    groups = set()
    evidence = {'ok': False, 'kind': 'real-process-manager-sigterm-smoke', 'proof_claim': False}
    started = time.monotonic()
    deadline = started + 8
    failure = None
    try:
        with (output / 'smoke-manager.log').open('w') as log:
            manager = subprocess.Popen(
                [sys.executable, str(Path(__file__).with_name('manage.py')), 'sigterm-smoke', sys.executable, '-c', CHILD, str(pidfile)],
                stdout=log, stderr=subprocess.STDOUT, start_new_session=True,
                env={**os.environ, 'CBCL_VOTE_OUTPUT': str(output), 'CBCL_JOLT_TARGET': str(output)},
            )
            groups.add(manager.pid)
            while not pidfile.exists():
                if manager.poll() is not None:
                    raise AssertionError('manager exited before the child PID handshake')
                if time.monotonic() > started + 2:
                    raise TimeoutError('child PID handshake exceeded two seconds')
                time.sleep(0.025)
            pids = json.loads(pidfile.read_text())
            groups.update([pids['child_pgid'], pids['detached_pgid']])
            evidence['pids'] = {'manager_pid': manager.pid, **pids}
            assert pids['child_pid'] == pids['child_pgid'], 'managed child must lead its own group'
            assert pids['detached_pid'] == pids['detached_pgid'], 'detached child must lead a distinct group'
            assert len(groups) == 3 and os.getpgrp() not in groups, 'unsafe or non-distinct group identities'
            # Manager samples every two seconds. Keep all groups alive through a
            # full subsequent sample before exercising the interruption path.
            time.sleep(2.3)
            assert all(group_exists(group) for group in groups), 'fixture exited before interruption'
            os.kill(manager.pid, signal.SIGTERM)
            code = manager.wait(timeout=max(0.1, deadline - time.monotonic()))
            evidence['manager_exit_code'] = code
            assert code != 0, 'interrupted manager incorrectly reported success'
            ledger = json.loads((output / 'sigterm-smoke-run.json').read_text())
            evidence['manager_ledger'] = ledger
            assert ledger['limit_reason'] == 'monitor interrupted: manager interrupted', 'expected SIGTERM interruption reason missing'
            assert ledger['exit_code'] == 23, 'managed child did not observe SIGTERM and reap its child'
            observed = set(ledger['observed_process_groups'])
            assert {pids['child_pgid'], pids['detached_pgid']} <= observed, 'manager did not observe both descendant groups'
            # Permit the OS a bounded interval to finish reaping after wait().
            while any(group_exists(group) for group in groups) and time.monotonic() < deadline:
                time.sleep(0.025)
            assert not any(group_exists(group) for group in groups), 'a manager/child/detached process group survived'
            evidence['groups_gone_before_test_cleanup'] = True
            evidence['ok'] = True
    except (AssertionError, OSError, ValueError, TimeoutError, subprocess.SubprocessError, KeyboardInterrupt) as error:
        failure = str(error) or type(error).__name__
        evidence['error'] = failure
    finally:
        # Never use our fallback to satisfy the assertions above. It runs only
        # after the verdict, including when a broken manager leaves descendants.
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        if manager is not None:
            try:
                groups.update(discovered_groups(manager.pid))
            except (OSError, subprocess.SubprocessError):
                pass
        if pidfile.exists():
            try:
                saved = json.loads(pidfile.read_text())
                groups.update([saved['child_pgid'], saved['detached_pgid']])
            except (OSError, ValueError, KeyError):
                pass
        # Only process groups from this isolated fixture; never signal ourselves.
        for group in groups - {os.getpgrp()}:
            try:
                os.killpg(group, signal.SIGKILL)
            except ProcessLookupError:
                pass
        if manager is not None:
            try:
                manager.wait(timeout=0.5)
            except subprocess.TimeoutExpired:
                evidence['cleanup_error'] = 'manager did not reap after SIGKILL'
                evidence['ok'] = False
        evidence['seconds'] = time.monotonic() - started
        evidence['output_dir'] = str(output)
        (output / 'smoke-result.json').write_text(json.dumps(evidence, indent=2) + '\n')
    print(json.dumps(evidence), flush=True)
    return 0 if evidence['ok'] else 1


if __name__ == '__main__':
    def interrupted(_signal, _frame):
        raise KeyboardInterrupt('smoke interrupted')
    signal.signal(signal.SIGTERM, interrupted)
    raise SystemExit(main())
