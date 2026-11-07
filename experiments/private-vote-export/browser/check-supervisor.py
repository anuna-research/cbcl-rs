#!/usr/bin/env python3
"""Real-process supervision regressions, without Chrome/Cargo/proofs.

Cases: runner dies before group registration, runner dies after publication,
a lowered real time cap interrupts publication, and a clean positive control.
Every assertion precedes
fallback cleanup, and every case retains its process/manager evidence.
"""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import uuid

HELPER = r'''
import json, os, pathlib, signal, subprocess, sys, time
runner, case, output = pathlib.Path(sys.argv[1]), sys.argv[2], pathlib.Path(sys.argv[3])
ns = {'__file__': str(runner), '__name__': 'supervisor_smoke_fixture'}
exec(compile(runner.read_text(), str(runner), 'exec'), ns)
ns['supervisor_request']({'kind':'run', 'mode':'prove', 'output': str(output)})
work = "import pathlib,time; p=pathlib.Path(" + repr(str(output)) + "); (p/'executed').write_text('public-fixture'); [(p/n).write_bytes(b'public smoke bytes, not a proof') for n in ['browser-proof.bin','browser-io.bin','browser-proof.bin.pending','browser-io.bin.pending']]; time.sleep(60)"
if case == 'before-registration':
    # Delay BEFORE entering the exact production bootstrap. Kill the runner in
    # that known window, before the manager's next two-second process sample.
    wrapper = "import pathlib,sys,time; p=pathlib.Path(sys.argv[1]); ns={'__file__':str(p),'__name__':'delayed_bootstrap'}; exec(compile(p.read_text(),str(p),'exec'),ns); time.sleep(.3); ns['supervised_exec']('chrome',sys.argv[2:])"
    fd = int(os.environ['CBCL_BROWSER_SUPERVISOR_FD'])
    worker = subprocess.Popen([sys.executable, '-c', wrapper, str(runner), sys.executable, '-c', work], start_new_session=True, pass_fds=(fd,))
else:
    worker = ns['launch_group']([sys.executable, '-c', work], 'chrome', sys.stdout)
value = {'runner_pid': os.getpid(), 'runner_pgid': os.getpgrp(), 'worker_pid': worker.pid, 'worker_pgid': os.getpgid(worker.pid)}
tmp=output/'pids.tmp'; tmp.write_text(json.dumps(value)); os.replace(tmp,output/'pids.json')
if case == 'before-registration':
    os.kill(os.getpid(), signal.SIGKILL)
while not (output/'executed').exists():
    if worker.poll() is not None: raise SystemExit('worker exited before work')
    time.sleep(.01)
# Simulate a successful backend/publication report before runner termination.
(output/'prove-result.json').write_text('{"ok":true,"exported":true}')
(output/'prove-runner.json').write_text('{"ok":true}')
if case == 'after-publication':
    os.kill(os.getpid(), signal.SIGKILL)
if case == 'clean-exit':
    (output/'browser-proof.bin.pending').unlink(); (output/'browser-io.bin.pending').unlink()
    raise SystemExit(0)
def stop(_signal,_frame):
    try: worker.wait(timeout=1.5)
    except subprocess.TimeoutExpired: pass
    raise SystemExit(23)
signal.signal(signal.SIGTERM,stop)
while True: time.sleep(1)
'''


def group_exists(group):
    try:
        os.killpg(group, 0)
        return True
    except ProcessLookupError:
        return False


def case_test(source, base, case):
    output = base / case
    output.mkdir()
    manager = None
    groups = set()
    started = time.monotonic()
    result = {'case': case, 'ok': False, 'proof_claim': False}
    try:
        with (output / 'test-manager.log').open('w') as log:
            manager = subprocess.Popen([sys.executable, str(source / 'manage.py'), 'supervision', sys.executable, '-c', HELPER, str(source / 'run-browser.py'), case, str(output)],
                stdout=log, stderr=subprocess.STDOUT, start_new_session=True,
                env={**os.environ, 'CBCL_VOTE_OUTPUT': str(output), 'CBCL_JOLT_TARGET': str(output), 'CBCL_BROWSER_TIME_LIMIT_SECONDS': '0.8' if case == 'time-cap' else '6'})
            groups.add(manager.pid)
            code = manager.wait(timeout=8)
        pids = json.loads((output / 'pids.json').read_text())
        groups.update([pids['runner_pgid'], pids['worker_pgid']])
        result['pids'] = {'manager_pid': manager.pid, **pids}
        ledger = json.loads((output / 'supervision-run.json').read_text())
        marker = json.loads((output / 'prove-supervisor.json').read_text())
        result['ledger'] = ledger
        result['marker'] = marker
        if case == 'clean-exit':
            assert code == 0 and ledger['ok'] is True, 'clean fixture failed manager success control'
            assert marker['ok'] is True and marker['status'] == 'complete', 'clean success marker missing'
            assert all((output / name).read_bytes() == b'public smoke bytes, not a proof' for name in ['browser-proof.bin', 'browser-io.bin']), 'clean public fixture not retained'
        else:
            assert code == 1 and ledger['ok'] is False, 'expected manager failure verdict'
            assert marker['ok'] is False and marker['status'] == 'failed', 'missing authoritative failure marker'
            assert not any((output / name).exists() for name in ['browser-proof.bin', 'browser-io.bin', 'browser-proof.bin.pending', 'browser-io.bin.pending']), 'public artifact survived failed run'
        if case == 'before-registration':
            assert ledger['exit_code'] == -signal.SIGKILL, 'runner death was not exercised'
            assert not (output / 'executed').exists(), 'work executed without group ACK'
            assert not ledger['registered_process_groups'], 'early-death fixture accidentally registered'
            assert pids['worker_pgid'] not in ledger['observed_process_groups'], 'fixture did not exercise the unsampled registration gap'
        else:
            assert (output / 'executed').exists(), 'publication did not happen before failure'
            assert pids['worker_pgid'] in ledger['registered_process_groups'], 'work ran without registered group'
            if case == 'time-cap':
                assert ledger['limit_reason'] == 'configured process time limit', 'real time cap was not exercised'
                assert ledger['exit_code'] == 23, 'fixture did not reap on manager TERM'
            elif case == 'after-publication':
                assert ledger['exit_code'] == -signal.SIGKILL, 'post-publication runner death not exercised'
            else:
                assert ledger['exit_code'] == 0 and ledger['limit_reason'] is None, 'clean fixture did not exit normally'
        deadline = started + 8.5
        while any(group_exists(group) for group in groups) and time.monotonic() < deadline:
            time.sleep(.025)
        assert not any(group_exists(group) for group in groups), 'process group survived before fallback cleanup'
        result['groups_gone_before_fallback'] = True
        result['ok'] = True
    except (AssertionError, OSError, ValueError, KeyError, subprocess.SubprocessError, KeyboardInterrupt) as error:
        result['error'] = str(error) or type(error).__name__
    finally:
        # Read handshake even after an assertion failure or timeout.
        if (output / 'pids.json').exists():
            saved = json.loads((output / 'pids.json').read_text())
            groups.update([saved['runner_pgid'], saved['worker_pgid']])
        for group in groups - {os.getpgrp()}:
            try:
                os.killpg(group, signal.SIGKILL)
            except ProcessLookupError:
                pass
        if manager is not None:
            try:
                manager.wait(timeout=.5)
            except subprocess.TimeoutExpired:
                result['ok'] = False
                result['cleanup_error'] = 'manager did not reap'
        result['seconds'] = time.monotonic() - started
        (output / 'test-result.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def main():
    source = Path(__file__).resolve().parent
    root = source.parents[2]
    base = root / 'outputs/jolt-dory-browser' / ('supervisor-smoke-' + uuid.uuid4().hex[:12])
    base.mkdir(parents=True)
    results = [case_test(source, base, case) for case in ['before-registration', 'after-publication', 'time-cap', 'clean-exit']]
    summary = {'ok': all(item['ok'] for item in results), 'proof_claim': False, 'results': results, 'output': str(base)}
    (base / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary), flush=True)
    return 0 if summary['ok'] else 1


if __name__ == '__main__':
    def interrupted(_signal, _frame):
        raise KeyboardInterrupt('smoke interrupted')
    signal.signal(signal.SIGTERM, interrupted)
    raise SystemExit(main())
