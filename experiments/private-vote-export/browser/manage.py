"""Sampled experiment limits with pre-exec group registration and artifact verdicts."""
import argparse
import json
import os
from pathlib import Path
import select
import shutil
import signal
import socket
import subprocess
import time

MODES = {'verify', 'count', 'prove', 'cancel-trace', 'cancel-prove'}
PUBLIC_ARTIFACTS = ('browser-proof.bin', 'browser-io.bin', 'browser-proof.bin.pending', 'browser-io.bin.pending')


def write_json(path, value):
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    os.replace(temporary, path)


def interrupted(_signal, _frame):
    raise KeyboardInterrupt('manager interrupted')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('label')
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if not args.label.replace('-', '').isalnum() or not args.command:
        parser.error('alphanumeric/hyphen label and command required')
    root = Path(__file__).resolve().parents[3]
    output = Path(os.environ.get('CBCL_VOTE_OUTPUT', root / 'outputs/jolt-dory-browser')).resolve()
    output.mkdir(parents=True, exist_ok=True)
    ledger_path = output / (args.label + '-run.json')
    if ledger_path.exists():
        parser.error('unique run label required')
    # A caller can lower the local time budget, never raise the 30-minute cap.
    time_limit = float(os.environ.get('CBCL_BROWSER_TIME_LIMIT_SECONDS', '1800'))
    if not 0 < time_limit <= 1800:
        parser.error('time limit must be positive and at most 1800 seconds')
    volumes = (root, output, Path(os.environ.get('CBCL_JOLT_TARGET', '/Users/anuna-02/Code/cbcl-rs-jolt-akita/experiments/jolt-akita-checkpoint/target')))
    started = time.monotonic()
    minimum = min(shutil.disk_usage(path).free for path in volumes)
    if minimum < 1024**3:
        raise SystemExit('preflight disk reserve below 1 GiB')
    peak = 0
    reason = None
    code = None
    child = None
    groups = set()
    registered = set()
    registrations = []
    cleanup_errors = []
    cleanup_warnings = []
    run = None
    buffer = b''
    monitor, endpoint = socket.socketpair()
    monitor_open = True
    signal.signal(signal.SIGTERM, interrupted)

    def register(message):
        nonlocal run
        if not isinstance(message, dict) or message.get('v') != 1 or not isinstance(message.get('nonce'), str):
            raise ValueError('invalid supervisor message')
        if child.poll() is not None:
            raise ValueError('runner exited before registration')
        if message.get('kind') == 'run':
            if set(message) != {'v', 'nonce', 'kind', 'mode', 'output'} or run is not None or message['mode'] not in MODES:
                raise ValueError('invalid or duplicate run registration')
            directory = Path(message['output']).resolve()
            # Cleanup paths must be explicitly inside this manager's evidence root.
            if not directory.is_relative_to(output):
                raise ValueError('runner output must be within CBCL_VOTE_OUTPUT')
            directory.mkdir(parents=True, exist_ok=True)
            marker = directory / (message['mode'] + '-supervisor.json')
            if marker.exists() or any((directory / name).exists() for name in PUBLIC_ARTIFACTS):
                raise ValueError('stale supervisor marker or public artifacts')
            run = {'mode': message['mode'], 'output': str(directory), 'marker': str(marker)}
            # Durable negative/default verdict exists before any work is released.
            write_json(marker, {**run, 'ok': False, 'status': 'running', 'manager_ledger': str(ledger_path)})
        elif message.get('kind') == 'group':
            if set(message) != {'v', 'nonce', 'kind', 'pid', 'pgid', 'parent_pid', 'role'} or run is None:
                raise ValueError('group registration before run or invalid shape')
            pid, pgid = message['pid'], message['pgid']
            if type(pid) is not int or pid != pgid or message['parent_pid'] != child.pid or message['role'] not in {'chrome', 'cdp'}:
                raise ValueError('invalid group identity or role')
            if pgid == os.getpgrp() or os.getpgid(pid) != pgid:
                raise ValueError('unsafe group identity')
            # Record BEFORE ACK. The bootstrap cannot exec Chrome/Node before it.
            groups.add(pgid)
            registered.add(pgid)
        else:
            raise ValueError('unknown supervisor message kind')
        registrations.append(message)
        return {'v': 1, 'nonce': message['nonce'], 'ok': True}

    def read_control():
        nonlocal buffer, monitor_open
        data = monitor.recv(4096)
        if not data:
            monitor_open = False
            return
        buffer += data
        if len(buffer) > 8192:
            raise ValueError('supervisor frame exceeds bound')
        while b'\n' in buffer:
            line, buffer = buffer.split(b'\n', 1)
            reply = register(json.loads(line))
            monitor.sendall(json.dumps(reply, separators=(',', ':')).encode() + b'\n')

    try:
        with (output / (args.label + '.log')).open('w') as log:
            child = subprocess.Popen(args.command, stdout=log, stderr=subprocess.STDOUT,
                start_new_session=True, pass_fds=(endpoint.fileno(),),
                env={**os.environ, 'CBCL_BROWSER_SUPERVISOR_FD': str(endpoint.fileno()), 'RAYON_NUM_THREADS': '4', 'CARGO_BUILD_JOBS': '1', 'CARGO_INCREMENTAL': '0', 'RUSTUP_TOOLCHAIN': '1.95.0'})
            groups.add(child.pid)
            endpoint.close()
            next_sample = 0
            while child.poll() is None:
                now = time.monotonic()
                if now - started > time_limit:
                    reason = '30-minute process limit' if time_limit == 1800 else 'configured process time limit'
                    break
                if now >= next_sample:
                    rows = subprocess.check_output(['ps', '-axo', 'pid=,ppid=,pgid=,rss='], text=True, timeout=5).splitlines()
                    rows = [tuple(map(int, row.split())) for row in rows if len(row.split()) == 4]
                    ids = {child.pid} | {pid for pid, _, pgid, _ in rows if pgid in groups}
                    while True:
                        expanded = ids | {pid for pid, ppid, _, _ in rows if ppid in ids}
                        if expanded == ids:
                            break
                        ids = expanded
                    groups.update(pgid for pid, _, pgid, _ in rows if pid in ids)
                    rss = sum(value * 1024 for pid, _, pgid, value in rows if pid in ids or pgid in groups)
                    peak = max(peak, rss)
                    minimum = min(minimum, *(shutil.disk_usage(path).free for path in volumes))
                    if rss > 4 * 1024**3:
                        reason = 'sampled process tree RSS exceeded 4 GiB'
                        break
                    if minimum < 1024**3:
                        reason = 'disk reserve below 1 GiB'
                        break
                    next_sample = now + 2
                if monitor_open and select.select([monitor], [], [], 0.05)[0]:
                    read_control()
                elif not monitor_open:
                    time.sleep(0.05)
    except BaseException as error:
        reason = 'monitor interrupted: ' + (str(error) or type(error).__name__)
    finally:
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        # Close before signaling: a not-yet-registered bootstrap sees EOF and can
        # never receive permission to exec, even if its runner died before ps.
        monitor.close()
        endpoint.close()
        for group in sorted(groups):
            try:
                os.killpg(group, signal.SIGTERM)
            except ProcessLookupError:
                pass
            except PermissionError as error:
                if child is not None and child.poll() is not None:
                    cleanup_warnings.append({'pgid': group, 'signal': 'SIGTERM', 'error': str(error)})
                else:
                    cleanup_errors.append({'pgid': group, 'signal': 'SIGTERM', 'error': str(error)})
        if child is not None:
            try:
                child.wait(timeout=3)
            except subprocess.TimeoutExpired:
                pass
        for group in sorted(groups):
            try:
                os.killpg(group, signal.SIGKILL)
            except ProcessLookupError:
                pass
            except PermissionError as error:
                if child is not None and child.poll() is not None:
                    cleanup_warnings.append({'pgid': group, 'signal': 'SIGKILL', 'error': str(error)})
                else:
                    cleanup_errors.append({'pgid': group, 'signal': 'SIGKILL', 'error': str(error)})
        if child is not None:
            try:
                code = child.wait(timeout=2)
            except subprocess.TimeoutExpired:
                reason = reason or 'manager could not reap its child'
    ok = code == 0 and reason is None and not cleanup_errors
    if run is not None:
        directory = Path(run['output'])
        if ok:
            try:
                runner = json.loads((directory / (run['mode'] + '-runner.json')).read_text())
                if runner.get('ok') is not True:
                    raise ValueError('runner success ledger missing')
            except (OSError, ValueError) as error:
                reason = str(error)
                ok = False
        if not ok:
            for name in PUBLIC_ARTIFACTS:
                try:
                    (directory / name).unlink(missing_ok=True)
                except OSError as error:
                    cleanup_errors.append({'artifact': name, 'error': str(error)})
        write_json(Path(run['marker']), {**run, 'ok': ok, 'status': 'complete' if ok else 'failed', 'manager_ledger': str(ledger_path), 'error': reason or (None if ok else 'runner failed'), 'cleanup_errors': cleanup_errors})
    result = {'command': args.command, 'exit_code': code, 'ok': ok, 'seconds': time.monotonic() - started, 'peak_observed_tree_rss_bytes': peak, 'rss_sampling_seconds': 2, 'minimum_free_bytes': minimum, 'limit_reason': reason, 'rayon_threads': 4, 'mock_proofs': False, 'observed_process_groups': sorted(groups), 'registered_process_groups': sorted(registered), 'registrations': registrations, 'browser_run': run, 'cleanup_errors': cleanup_errors, 'cleanup_warnings': cleanup_warnings, 'time_limit_seconds': time_limit}
    write_json(ledger_path, result)
    print(json.dumps(result), flush=True)
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(main())
