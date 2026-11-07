#!/usr/bin/env python3
"""Loopback-only browser experiment: python3 run-browser.py MODE OUTPUT_DIR."""
from __future__ import annotations

import json
import math
import os
from pathlib import Path
import shutil
import signal
import socket
import uuid
import subprocess
import sys
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlsplit

MODES = {"verify", "count", "prove", "cancel-trace", "cancel-prove"}
SOURCE = Path(__file__).resolve().parent
FIXTURES = Path(os.environ.get("CBCL_VOTE_FIXTURES", "/Users/anuna-02/Code/cbcl-rs-private-vote/outputs/private-vote-export")).expanduser().resolve()
TIMEOUT = 25 * 60
MAX_JSON = 1024 * 1024


def ordinary_json(raw: bytes):
    def unique(pairs):
        obj = {}
        for key, value in pairs:
            if key in obj:
                raise ValueError("duplicate JSON member")
            obj[key] = value
        return obj

    def invalid(_):
        raise ValueError("nonfinite JSON number")

    value = json.loads(raw.decode("utf-8"), object_pairs_hook=unique, parse_constant=invalid)
    forbidden = {"witness", "private", "private_input", "private_inputs", "salt", "secret", "secret_key", "private_key", "ballots", "discussion", "signatures"}

    def check(item, depth=0):
        if depth > 24:
            raise ValueError("JSON nesting limit")
        if isinstance(item, dict):
            for key, child in item.items():
                if key.lower().replace("-", "_") in forbidden:
                    raise ValueError("private field prohibited in metrics")
                check(child, depth + 1)
        elif isinstance(item, list):
            if len(item) > 4096:
                raise ValueError("metrics array limit")
            for child in item:
                check(child, depth + 1)
        elif isinstance(item, float) and not math.isfinite(item):
            raise ValueError("nonfinite JSON number")
        elif not isinstance(item, (str, int, float, bool, type(None))):
            raise ValueError("ordinary JSON required")
    check(value)
    if not isinstance(value, dict):
        raise ValueError("metrics must be a JSON object")
    return value


def validate_result(mode, result):
    if not isinstance(result, dict) or result.get("ok") is not True:
        raise ValueError("experiment returned a failing result")
    if mode.startswith("cancel-"):
        recovery = result.get("recovery")
        if result.get("cancelled") is not True or not isinstance(recovery, dict) or recovery.get("ok") is not True or recovery.get("verified") is not True:
            raise ValueError("cancellation requires cancellation and fresh-worker verification recovery")


def assets(output):
    # No path from an HTTP request is ever joined to a filesystem directory.
    table = {
        "/": SOURCE / "index.html",
        "/index.html": SOURCE / "index.html",
        "/app.js": SOURCE / "app.js",
        "/worker.js": SOURCE / "worker.js",
        "/pkg/cbcl_vote_browser.js": output / "pkg/cbcl_vote_browser.js",
        "/pkg/cbcl_vote_browser_bg.wasm": output / "pkg/cbcl_vote_browser_bg.wasm",
        "/assets/prover-setup.bin": output / "profile/prover-setup.bin",
        "/assets/profile.json": output / "profile/profile.json",
    }
    fixed = {
        "over-cap.json": "scale-16/input.json",
        "over-cap-expected.json": "scale-16/expected.json",
        "setup.bin": "zk-proof/setup.bin",
        "proof.bin": "zk-proof/proof.bin",
        "io.bin": "zk-proof/io.bin",
        "expected.json": "fixture/expected.json",
        "trusted.json": "operator-pins/zk/trusted.json",
        "clear-proof.bin": "clear-proof/proof.bin",
        "witness.json": "fixture/input.json",
        "missing-closure.json": "negative-fixtures/cases/missingclosure.json",
        "bad-signature.json": "negative-fixtures/cases/invalidmsgsig.json",
        "advice-io.bin": "zk-receiver-cases/advice-io.bin",
        "coherent-io.bin": "zk-receiver-cases/changed-io.bin",
        "coherent-expected.json": "zk-receiver-cases/coherent-tally.json",
        "guest.elf": "guest-target/cbcl-vote-guest-export_vote/riscv64imac-unknown-none-elf/release/cbcl-vote-guest",
    }
    table.update({"/assets/" + name: FIXTURES / relative for name, relative in fixed.items()})
    # Snapshot generated assets before listening; HTTP never resolves client paths.
    pkg = (output / "pkg").resolve()
    for file in sorted((output / "pkg").rglob("*")):
        if file.is_file():
            resolved = file.resolve()
            if not resolved.is_relative_to(pkg):
                raise ValueError("generated package symlink leaves pkg directory")
            table["/pkg/" + file.relative_to(output / "pkg").as_posix()] = resolved
    return table


class State:
    def __init__(self, output, mode):
        self.output, self.mode = output, mode
        self.lock = threading.Lock()
        self.result = None
        self.errors = []
        self.artifacts = set()
        self.stopping = False
        self.origin = ""
        self.table = assets(output)

    def error(self, text):
        with self.lock:
            self.errors.append(text)


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def setup(self):
        super().setup()
        self.connection.settimeout(15)

    @property
    def state(self):
        return self.server.state

    def log_message(self, *_):
        pass  # Request bodies/fixture bytes never enter the HTTP log.

    def respond(self, status, body=b"", mime="text/plain; charset=utf-8"):
        self.send_response(status)
        self.send_header("Content-Type", mime)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Cross-Origin-Opener-Policy", "same-origin")
        self.send_header("Cross-Origin-Embedder-Policy", "require-corp")
        self.send_header("Cross-Origin-Resource-Policy", "same-origin")
        self.send_header("Content-Security-Policy", "default-src 'none'; script-src 'self' 'wasm-unsafe-eval'; worker-src 'self'; connect-src 'self'; style-src 'self' 'unsafe-inline'; img-src 'self'; base-uri 'none'; frame-ancestors 'none'; form-action 'none'")
        self.send_header("Connection", "close")
        self.end_headers()
        self.close_connection = True
        if body:
            self.wfile.write(body)

    def permitted(self, post=False):
        if self.headers.get("Host") != urlsplit(self.state.origin).netloc:
            self.respond(403)
            return False
        origin = self.headers.get("Origin")
        if (post and origin != self.state.origin) or (origin is not None and origin != self.state.origin):
            self.respond(403)
            return False
        return True

    def do_GET(self):
        if not self.permitted():
            return
        path = self.path  # Exact keys: queries, encoded traversal and aliases reject.
        if path == "/favicon.ico":
            self.respond(204)  # Browser-generated request; no asset or filesystem read.
            return
        file = self.state.table.get(path)
        if file is None:
            self.state.error("unallowlisted GET: " + path[:256])
            self.respond(404)
            return
        if not file.is_file():
            self.state.error("missing allowlisted asset: " + path)
            self.respond(404)
            return
        mime = {".js": "text/javascript; charset=utf-8", ".html": "text/html; charset=utf-8", ".json": "application/json; charset=utf-8", ".wasm": "application/wasm"}.get(file.suffix, "application/octet-stream")
        try:
            self.respond(200, file.read_bytes(), mime)
        except (OSError, TimeoutError) as error:
            self.state.error("asset transfer failed: " + type(error).__name__)

    def do_POST(self):
        if not self.permitted(post=True):
            return
        limits = {"/artifact/proof": 1024 * 1024, "/artifact/io": 16 * 1024, "/phase": 16 * 1024, "/result": MAX_JSON}
        limit = limits.get(self.path)
        if limit is None:
            self.state.error("unallowlisted POST")
            self.respond(404)
            return
        length = self.headers.get_all("Content-Length", [])
        if self.headers.get("Transfer-Encoding") or len(length) != 1 or not length[0].isascii() or not length[0].isdigit():
            self.state.error("invalid request framing")
            self.respond(400)
            return
        if len(length[0]) > 10:
            self.state.error("oversized Content-Length")
            self.respond(413)
            return
        size = int(length[0])
        if size < 1 or size > limit:
            self.state.error("request exceeds endpoint size limit")
            self.respond(413)
            return
        try:
            body = self.rfile.read(size)
            if len(body) != size:
                raise ValueError("truncated body")
            with self.state.lock:
                if self.state.stopping:
                    raise ValueError("run already stopped")
                if self.path.startswith("/artifact/"):
                    if self.state.mode != "prove":
                        raise ValueError("artifact publication only allowed in prove mode")
                    kind = self.path.rsplit("/", 1)[1]
                    if kind in self.state.artifacts:
                        raise ValueError("duplicate artifact")
                    (self.state.output / ("browser-" + kind + ".bin")).write_bytes(body)
                    self.state.artifacts.add(kind)
                else:
                    value = ordinary_json(body)
                    if self.path == "/phase":
                        if "phase" not in value and value.get("type") == "phase":
                            value["phase"] = value.get("name")
                        if not isinstance(value.get("phase"), str):
                            raise ValueError("phase string required")
                        line = json.dumps(value, allow_nan=False, separators=(",", ":"))
                        with (self.state.output / (self.state.mode + "-phases.jsonl")).open("a") as stream:
                            stream.write(line + "\n")
                        print(line, flush=True)
                    else:
                        if self.state.result is not None:
                            raise ValueError("duplicate result")
                        (self.state.output / (self.state.mode + "-result.json")).write_text(json.dumps(value, allow_nan=False, indent=2) + "\n")
                        self.state.result = value
            self.respond(200, b"{}", "application/json")
        except (ValueError, RecursionError, OSError, TimeoutError) as error:
            self.state.error("POST rejected: " + str(error)[:200])
            self.respond(400)


def supervisor_request(message):
    """One bounded request/ACK on a private inherited supervisor descriptor."""
    descriptor = os.environ.get("CBCL_BROWSER_SUPERVISOR_FD")
    if descriptor is None:
        return None
    request = {"v": 1, "nonce": uuid.uuid4().hex, **message}
    raw = json.dumps(request, separators=(",", ":")).encode() + b"\n"
    if len(raw) > 4096:
        raise ValueError("supervisor request exceeds bound")
    with socket.fromfd(int(descriptor), socket.AF_UNIX, socket.SOCK_STREAM) as control:
        control.settimeout(5)
        control.sendall(raw)
        reply = b""
        while not reply.endswith(b"\n"):
            part = control.recv(1)
            if not part:
                raise RuntimeError("supervisor closed before ACK")
            reply += part
            if len(reply) > 4096:
                raise ValueError("supervisor ACK exceeds bound")
    value = json.loads(reply)
    if value != {"v": 1, "nonce": request["nonce"], "ok": True}:
        raise RuntimeError("invalid supervisor ACK")
    return value


def supervised_exec(role, command):
    """Bootstrap: no Chrome/Node work before our own PGID is acknowledged."""
    descriptor = os.environ.get("CBCL_BROWSER_SUPERVISOR_FD")
    if descriptor is None or role not in {"chrome", "cdp"} or not command:
        raise ValueError("invalid supervised bootstrap invocation")
    supervisor_request({"kind": "group", "pid": os.getpid(), "pgid": os.getpgrp(), "parent_pid": os.getppid(), "role": role})
    # Browser/Node must not inherit the private management channel.
    os.close(int(descriptor))
    environment = dict(os.environ)
    environment.pop("CBCL_BROWSER_SUPERVISOR_FD", None)
    os.execvpe(command[0], command, environment)


def launch_group(command, role, log):
    descriptor = os.environ.get("CBCL_BROWSER_SUPERVISOR_FD")
    if descriptor is None:
        return subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
    return subprocess.Popen([sys.executable, str(Path(__file__).resolve()), "--supervised-exec", role, *command],
        stdout=log, stderr=subprocess.STDOUT, start_new_session=True, pass_fds=(int(descriptor),))


def stop_group(process, warnings):
    if process is None:
        return
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    except PermissionError:
        if process.poll() is None:
            raise
        warnings.append({"pid": process.pid, "signal": "SIGTERM", "reason": "group permission denied after leader exit"})
        return
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        pass
    # Also reap descendants if the group leader exited before its children.
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    except PermissionError:
        if process.poll() is None:
            raise
        warnings.append({"pid": process.pid, "signal": "SIGKILL", "reason": "group permission denied after leader exit"})
    process.wait(timeout=5)


def main():
    if len(sys.argv) != 3 or sys.argv[1] not in MODES:
        print("usage: run-browser.py {verify,count,prove,cancel-trace,cancel-prove} OUTPUT_DIR", file=sys.stderr)
        return 2
    mode, output = sys.argv[1], Path(sys.argv[2]).resolve()
    output.mkdir(parents=True, exist_ok=True)
    state = State(output, mode)
    chrome = os.environ.get("CHROME") or next((p for p in ["/Applications/Google Chrome.app/Contents/MacOS/Google Chrome", shutil.which("chromium"), shutil.which("chromium-browser"), shutil.which("google-chrome")] if p and Path(p).is_file()), None)
    node = shutil.which("node")
    if not chrome or not node:
        print("existing Chrome/Chromium and Node 25+ are required", file=sys.stderr)
        return 2
    version = subprocess.check_output([node, "--version"], text=True).strip()
    if int(version.lstrip("v").split(".")[0]) < 25:
        print("Node 25+ native WebSocket required", file=sys.stderr)
        return 2
    # Refuse stale artifacts/ledgers rather than confusing two runs' evidence.
    paths = [output / (mode + suffix) for suffix in ["-result.json", "-phases.jsonl", "-cdp.json", "-harness.log", "-chrome.log", "-runner.json", "-supervisor.json"]]
    if any(path.exists() for path in paths) or any((output / name).exists() for name in ["browser-proof.bin", "browser-io.bin"]):
        print("use a fresh run output directory (with pkg/profile assets staged)", file=sys.stderr)
        return 2
    supervisor_request({"kind": "run", "mode": mode, "output": str(output)})
    server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    server.daemon_threads = True
    server.state = state
    state.origin = "http://127.0.0.1:" + str(server.server_port)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    chrome_process = cdp_process = None
    started = time.monotonic()
    success = False
    failure = None
    cleanup_warnings = []
    cleanup_errors = []
    user_data = output / (mode + "-chrome-profile")
    try:
        with (output / (mode + "-chrome.log")).open("w") as chrome_log, (output / (mode + "-harness.log")).open("w") as harness_log:
            chrome_process = launch_group([chrome, "--headless=new", "--remote-debugging-port=0", "--remote-debugging-address=127.0.0.1", "--user-data-dir=" + str(user_data), "--no-first-run", "--no-default-browser-check", "--disable-background-networking", "--disable-component-update", "--disable-sync", "--disable-default-apps", "--disable-extensions", "--disable-domain-reliability", "--disable-client-side-phishing-detection", "--no-proxy-server", "--metrics-recording-only", "--host-resolver-rules=MAP * ~NOTFOUND, EXCLUDE 127.0.0.1", "about:blank"], "chrome", chrome_log)
            endpoint_file = user_data / "DevToolsActivePort"
            deadline = time.monotonic() + 30
            endpoint_lines = []
            while len(endpoint_lines) < 2:
                if chrome_process.poll() is not None:
                    raise RuntimeError("Chrome exited before CDP was ready")
                if time.monotonic() > deadline:
                    raise TimeoutError("Chrome CDP startup timeout")
                if endpoint_file.exists():
                    endpoint_lines = endpoint_file.read_text().splitlines()
                if len(endpoint_lines) < 2:
                    time.sleep(0.1)
            port, websocket_path = endpoint_lines[:2]
            if not port.isdigit() or not websocket_path.startswith("/devtools/browser/"):
                raise RuntimeError("invalid Chrome CDP endpoint")
            endpoint = "ws://127.0.0.1:" + port + websocket_path
            cdp_process = launch_group([node, str(SOURCE / "cdp.mjs"), endpoint, mode, str(output), state.origin], "cdp", harness_log)
            try:
                code = cdp_process.wait(timeout=TIMEOUT + 45)
            except subprocess.TimeoutExpired as error:
                raise TimeoutError("CDP outer timeout") from error
            if code != 0:
                raise RuntimeError("CDP failed; inspect " + mode + "-cdp.json and harness.log")
            validate_result(mode, state.result)
            cdp_record = json.loads((output / (mode + "-cdp.json")).read_text())
            if cdp_record.get("ok") is not True or cdp_record.get("result") != state.result:
                raise RuntimeError("CDP result differs from posted public result")
            if mode == "verify" and state.result.get("verified") is not True:
                raise RuntimeError("verify mode did not verify the native artifact")
            if mode == "prove" and (state.result.get("exported") is not True or state.result.get("recovery", {}).get("verified") is not True):
                raise RuntimeError("prove requires fresh verification and explicit export")
            if state.errors:
                raise RuntimeError("HTTP contract failure: " + state.errors[0])
            if mode == "prove" and state.artifacts != {"proof", "io"}:
                raise RuntimeError("prove requires both exported public artifacts")
            if mode.startswith("cancel-") and state.artifacts:
                raise RuntimeError("cancelled run published artifacts")
            success = True
    except (OSError, ValueError, RuntimeError, TimeoutError, KeyboardInterrupt) as error:
        failure = str(error) or type(error).__name__
        print(failure, file=sys.stderr, flush=True)
    finally:
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        with state.lock:
            state.stopping = True
        # Cleanup failures must not prevent other cleanup or the durable ledger.
        for name, process in (("cdp", cdp_process), ("chrome", chrome_process)):
            try:
                stop_group(process, cleanup_warnings)
            except (OSError, subprocess.SubprocessError) as error:
                cleanup_errors.append(name + ": " + type(error).__name__ + ": " + str(error))
        for name, action in (("server-shutdown", server.shutdown), ("server-close", server.server_close)):
            try:
                action()
            except OSError as error:
                cleanup_errors.append(name + ": " + str(error))
        thread.join(timeout=5)
        if thread.is_alive():
            cleanup_errors.append("HTTP server thread did not stop")
        if cleanup_errors:
            success = False
            failure = failure or "cleanup failed: " + cleanup_errors[0]
        if not success:
            # A failed/cancelled run cannot leave artifacts looking successful.
            for name in ("browser-proof.bin", "browser-io.bin"):
                (output / name).unlink(missing_ok=True)
        (output / (mode + "-runner.json")).write_text(json.dumps({"ok": success, "mode": mode, "elapsed_seconds": time.monotonic() - started, "error": failure, "http_errors": state.errors, "cleanup_warnings": cleanup_warnings, "cleanup_errors": cleanup_errors, "node": version, "chrome": chrome, "origin": state.origin, "memory_note": "WASM capacity is reported by worker phases; browser RSS is measured by outer manage.py"}, indent=2) + "\n")
        # Fresh synthetic profile has no lasting browser storage lifecycle.
        shutil.rmtree(user_data, ignore_errors=True)
    return 0 if success else 1


if __name__ == "__main__":
    if len(sys.argv) >= 3 and sys.argv[1] == "--supervised-exec":
        supervised_exec(sys.argv[2], sys.argv[3:])
        raise SystemExit("supervised exec unexpectedly returned")
    def interrupted(_signal, _frame):
        raise KeyboardInterrupt()
    signal.signal(signal.SIGTERM, interrupted)
    raise SystemExit(main())
