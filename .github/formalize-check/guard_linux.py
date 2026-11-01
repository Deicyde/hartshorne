"""Run one verification stage with the user's approved Linux process limits."""

import ctypes
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

import psutil

RSS_LIMIT = 6 * 1024**3
OUTPUT_LIMIT = 256 * 1024**2
DEADLINE_SECONDS = 600


def identity(process):
    fresh = psutil.Process(process.pid)
    return (fresh.pid, fresh.create_time())


def live(process, expected):
    try:
        if identity(process) != expected:
            return False
        return psutil.Process(process.pid).status() not in (psutil.STATUS_ZOMBIE, psutil.STATUS_DEAD)
    except psutil.NoSuchProcess:
        return False


def main():
    if sys.argv[1:2] == ["--worker"]:
        parent, gate, digest = int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
        if os.getppid() != parent or hashlib.sha256(Path(__file__).read_bytes()).hexdigest() != digest:
            raise RuntimeError("worker identity or guard bytes changed")
        if os.read(gate, 1) != b"G":
            raise RuntimeError("worker was not registered")
        os.close(gate)
        os.execvp(sys.argv[5], sys.argv[5:])
    if sys.platform != "linux":
        raise RuntimeError("this verification guard requires Linux")
    libc = ctypes.CDLL(None, use_errno=True)
    libc.prctl.argtypes = (ctypes.c_int, ctypes.c_ulong, ctypes.c_ulong, ctypes.c_ulong, ctypes.c_ulong)
    libc.prctl.restype = ctypes.c_int
    if libc.prctl(36, 1, 0, 0, 0) != 0:  # PR_SET_CHILD_SUBREAPER, no privilege required.
        raise OSError(ctypes.get_errno(), "cannot establish owned descendant adoption")
    receipt = Path(sys.argv[1])
    command = sys.argv[3:]
    if sys.argv[2] != "--" or not command or receipt.exists():
        raise ValueError("require a fresh receipt path followed by -- COMMAND")
    receipt.parent.mkdir(parents=True, exist_ok=True)
    stdout = receipt.with_suffix(".stdout")
    stderr = receipt.with_suffix(".stderr")
    if stdout.exists() or stderr.exists():
        raise ValueError("output paths already exist")
    start = time.monotonic()
    owned = {}
    errors = []
    cleanup_errors = []
    survivors = []
    peak = samples = 0
    process = None
    gate_read = gate_write = None
    interrupted = []
    handlers = {}

    def stop(signum, _frame):
        interrupted.append(signum)

    def remember(candidate):
        expected = identity(candidate)
        if expected[0] in owned and owned[expected[0]][1] != expected:
            raise RuntimeError("owned PID was reused")
        owned[expected[0]] = (candidate, expected)

    def discover():
        visited = set()
        pending = list(owned.values())
        while pending:
            parent, parent_identity = pending.pop()
            if parent.pid in visited or not live(parent, parent_identity):
                continue
            visited.add(parent.pid)
            for child in psutil.Process(parent.pid).children(recursive=False):
                try:
                    child_identity = identity(child)
                    child_parent = psutil.Process(child.pid).ppid()
                    if not live(parent, parent_identity):
                        raise RuntimeError("parent disappeared during descendant registration")
                    if child_parent != parent.pid or identity(child) != child_identity:
                        raise RuntimeError("descendant parent or identity changed before registration")
                    remember(child)
                    if owned[child.pid][1] != child_identity:
                        raise RuntimeError("descendant identity changed during registration")
                    pending.append(owned[child.pid])
                except psutil.NoSuchProcess:
                    # A disappeared PID is not retained or signaled.
                    continue

    def sample():
        nonlocal peak, samples
        # Discover only descendants of positively identified owned processes.
        discover()
        total = 0
        for candidate, expected in list(owned.values()):
            if not live(candidate, expected):
                continue
            try:
                resident = candidate.memory_info().rss
            except psutil.NoSuchProcess:
                if not live(candidate, expected):
                    continue
                raise
            if not live(candidate, expected):
                continue
            if resident <= 0:
                raise RuntimeError("live owned process has no positive RSS reading")
            total += resident
        peak = max(peak, total)
        samples += 1
        if total > RSS_LIMIT:
            raise RuntimeError("aggregate owned-process RSS exceeded 6 GiB")
        if stdout.stat().st_size + stderr.stat().st_size > OUTPUT_LIMIT:
            raise RuntimeError("combined output exceeded 256 MiB")
        if time.monotonic() - start > DEADLINE_SECONDS:
            raise RuntimeError("verification stage exceeded 600 seconds")
        if interrupted:
            raise RuntimeError("verification stage interrupted")

    try:
        for signum in (signal.SIGINT, signal.SIGTERM):
            handlers[signum] = signal.signal(signum, stop)
        supervisor = psutil.Process()
        remember(supervisor)
        gate_read, gate_write = os.pipe()
        with stdout.open("xb") as out, stderr.open("xb") as err:
            process = subprocess.Popen(
                [sys.executable, __file__, "--worker", str(os.getpid()), str(gate_read),
                 hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), *command],
                pass_fds=(gate_read,), stdout=out, stderr=err, start_new_session=True,
            )
            os.close(gate_read)
            gate_read = None
            worker = psutil.Process(process.pid)
            if worker.ppid() != os.getpid():
                raise RuntimeError("worker parent identity mismatch")
            remember(worker)
            sample()
            os.write(gate_write, b"G")
            os.close(gate_write)
            gate_write = None
            while process.poll() is None:
                sample()
                time.sleep(0.1)
            sample()
            if process.wait() != 0:
                raise RuntimeError(f"verification command exited {process.returncode}")
    except BaseException as exc:
        errors.append(f"{type(exc).__name__}: {exc}")
    finally:
        for descriptor in (gate_read, gate_write):
            if descriptor is not None:
                try:
                    os.close(descriptor)
                except BaseException as exc:
                    cleanup_errors.append(f"gate close: {type(exc).__name__}: {exc}")
        # Refresh descendants before cleanup; every failure retains a FAIL.
        def refresh_cleanup():
            try:
                discover()
            except BaseException as exc:
                cleanup_errors.append(f"discover: {type(exc).__name__}: {exc}")
            return [pair for pair in owned.values() if pair[0].pid != os.getpid()]

        def check_remaining():
            remaining = []
            for candidate, expected in refresh_cleanup():
                try:
                    if live(candidate, expected):
                        remaining.append((candidate, expected))
                except BaseException as exc:
                    cleanup_errors.append(f"check {candidate.pid}: {type(exc).__name__}: {exc}")
                    remaining.append((candidate, expected))
            return remaining

        initially_live = check_remaining()
        if initially_live and not errors:
            errors.append("command exited while owned descendants remained live")
        for candidate, expected in initially_live:
            try:
                if live(candidate, expected):
                    candidate.terminate()
            except BaseException as exc:
                cleanup_errors.append(f"TERM {candidate.pid}: {type(exc).__name__}: {exc}")
        finish = time.monotonic() + 2
        while time.monotonic() < finish and check_remaining():
            time.sleep(0.05)
        for candidate, expected in refresh_cleanup():
            try:
                if live(candidate, expected):
                    candidate.kill()
            except BaseException as exc:
                cleanup_errors.append(f"KILL {candidate.pid}: {type(exc).__name__}: {exc}")
        if process is not None:
            try:
                process.wait(timeout=5)
            except BaseException as exc:
                cleanup_errors.append(f"reap: {type(exc).__name__}: {exc}")
        finish = time.monotonic() + 2
        while time.monotonic() < finish and check_remaining():
            for candidate, expected in check_remaining():
                try:
                    if live(candidate, expected):
                        candidate.kill()
                except BaseException as exc:
                    cleanup_errors.append(f"late KILL {candidate.pid}: {type(exc).__name__}: {exc}")
            time.sleep(0.05)
        survivors = [list(expected) for _candidate, expected in check_remaining()]
        # Reap adopted direct children individually. Popen owns its worker reap.
        for candidate, expected in refresh_cleanup():
            if process is not None and candidate.pid == process.pid:
                continue
            try:
                if identity(candidate) == expected and psutil.Process(candidate.pid).ppid() == os.getpid():
                    result, _status = os.waitpid(candidate.pid, os.WNOHANG)
                    if result == 0:
                        cleanup_errors.append(f"adopted child {candidate.pid} was not reaped")
            except (psutil.NoSuchProcess, ChildProcessError):
                pass
            except BaseException as exc:
                cleanup_errors.append(f"adopted reap {candidate.pid}: {type(exc).__name__}: {exc}")
        survivors = [list(expected) for _candidate, expected in check_remaining()]
        try:
            if stdout.stat().st_size + stderr.stat().st_size > OUTPUT_LIMIT:
                errors.append("combined final output exceeded 256 MiB")
        except BaseException as exc:
            errors.append(f"final output check: {type(exc).__name__}: {exc}")
        for signum, previous in handlers.items():
            signal.signal(signum, previous)
    if interrupted and not errors:
        errors.append("interruption received during cleanup")
    passed = samples > 0 and not errors and not cleanup_errors and not survivors and process is not None and process.returncode == 0
    receipt.write_text(json.dumps({
        "schema": "hartshorne-linux-stage/v1", "status": "PASS" if passed else "FAIL",
        "command": command, "elapsed_seconds": time.monotonic() - start,
        "limits": {"rss_bytes": RSS_LIMIT, "output_bytes": OUTPUT_LIMIT, "seconds": DEADLINE_SECONDS},
        "peak_rss_bytes": peak, "samples": samples, "exit_code": None if process is None else process.returncode,
        "owned_identities": [list(pair[1]) for pair in owned.values()],
        "errors": errors, "cleanup_errors": cleanup_errors, "survivors": survivors,
    }, indent=2) + "\n")
    print(receipt.read_text())
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
