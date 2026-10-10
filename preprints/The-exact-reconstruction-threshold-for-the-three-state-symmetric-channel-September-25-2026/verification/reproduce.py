#!/usr/bin/env python3
"""Replay the three unchanged certificates, retaining every process result.

Requires Python 3.9+, SymPy (for pair.py), and g++ with C++17 and __int128.
The runner itself uses only the Python standard library. Example, from the article root:
  python3 verification/reproduce.py --output-dir checks/certificate-replay
The output directory must be new and outside verification/. No network is used.
"""

import argparse
import concurrent.futures
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import threading
import time


SOURCE_SHA256 = {
    "pair.py": "ab775c3a63fb1d2713bfe058af2dece4ceda99627c17ce18f51f817b69410bba",
    "interval.cpp": "76d1443b1194597ee77749e8030c825f2b9aae46b5c172d9eccf0745078c28e3",
    "grid.cpp": "03c92321efedd0db53b1e91372918dfcd68d459db0223cb160c39df3bd645283",
}
INTERVAL_VISITS = (414080, 756096, 1004426)
GRID_ITERATIONS = {
    -1: 162,
    0: 104, 1: 103, 2: 103, 3: 103,
    4: 102, 5: 102, 6: 102, 7: 102, 8: 102,
    9: 101, 10: 101, 11: 101, 12: 101, 13: 101, 14: 101,
    15: 100, 16: 100, 17: 100, 18: 100, 19: 100, 20: 100, 21: 100,
    22: 99, 23: 99, 24: 99, 25: 99, 26: 99,
}
COMPILE_FLAGS = ("-std=c++17", "-O3", "-UNDEBUG")


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, data):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def output_check(kind, argument, stdout, stderr):
    """Require the entire successful output shape, not merely a matching substring."""
    if kind == "pair":
        return {"passed": stdout == "" and stderr == "", "expected": "silent success"}
    if kind == "interval":
        lines = stderr.splitlines()
        matches = [re.fullmatch(r"(\d+),(\d+): (\d+)", line) for line in lines]
        valid = stdout == "" and len(matches) == 24 and all(matches)
        counts = []
        if valid:
            triples = [tuple(map(int, match.groups())) for match in matches]
            counts = [row[2] for row in triples]
            valid = (all(row[:2] == (argument, i) for i, row in enumerate(triples))
                     and all(a < b for a, b in zip([0] + counts, counts))
                     and counts[-1] == INTERVAL_VISITS[argument])
        return {"passed": bool(valid), "visits": counts[-1] if counts else None,
                "expected_visits": INTERVAL_VISITS[argument], "progress_rows": len(lines)}
    if kind == "grid":
        expected = f"{argument} {GRID_ITERATIONS[argument]}\n"
        lines = stderr.splitlines()
        table_modes = [2, 0] if argument == -1 else [1]
        tables_ok = len(lines) >= len(table_modes) and all(
            re.fullmatch(rf"table {mode} entries [1-9]\d*", line)
            for mode, line in zip(table_modes, lines))
        progress = lines[len(table_modes):]
        iterations = list(range(10, GRID_ITERATIONS[argument] + 1, 10))
        progress_ok = len(progress) == len(iterations) and all(
            re.fullmatch(rf"{argument} {iteration} [1-9]\d* [0-9.eE+-]+", line)
            for iteration, line in zip(iterations, progress))
        return {"passed": stdout == expected and tables_ok and progress_ok,
                "expected_stdout": expected, "actual_stdout": stdout,
                "expected_iterations": GRID_ITERATIONS[argument],
                "table_output_valid": bool(tables_ok), "progress_output_valid": progress_ok}
    if kind == "python_probe":
        try:
            info = json.loads(stdout)
            valid = info["assertions_enabled"] is True and bool(info["sympy_version"])
        except (ValueError, KeyError, TypeError):
            info, valid = None, False
        return {"passed": valid and stderr == "", "environment": info}
    if kind == "compiler_macros":
        macros = dict(re.findall(r"^#define (\w+)(?: (.*))?$", stdout, re.MULTILINE))
        return {"passed": "NDEBUG" not in macros and macros.get("__cplusplus") == "201703L"
                and macros.get("__SIZEOF_INT128__") == "16",
                "ndebug_defined": "NDEBUG" in macros,
                "cplusplus": macros.get("__cplusplus"), "sizeof_int128": macros.get("__SIZEOF_INT128__")}
    return {"passed": True, "expected": "zero process exit status"}


class Replay:
    def __init__(self, output, timeout):
        self.output = output
        self.timeout = timeout
        self.cancelled = threading.Event()
        self.lock = threading.Lock()
        self.active = set()

    def cancel(self):
        self.cancelled.set()
        with self.lock:
            for process in self.active:
                if process.poll() is None:
                    process.kill()

    def run(self, name, command, kind="command", argument=None, stdin=None):
        record = {"name": name, "command": command, "cwd": str(self.output),
                  "started_utc": now(), "status": "running", "returncode": None,
                  "stdout_file": name + ".stdout", "stderr_file": name + ".stderr"}
        result_path = self.output / (name + ".json")
        write_json(result_path, record)
        start = time.monotonic()
        process = None
        try:
            with (self.output / record["stdout_file"]).open("wb") as out, \
                    (self.output / record["stderr_file"]).open("wb") as err:
                with self.lock:
                    if self.cancelled.is_set():
                        raise RuntimeError("cancelled before launch")
                    process = subprocess.Popen(command, cwd=self.output, stdout=out, stderr=err,
                                               stdin=subprocess.PIPE if stdin is not None else subprocess.DEVNULL)
                    self.active.add(process)
                try:
                    process.communicate(input=stdin, timeout=self.timeout)
                    record["status"] = "completed"
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.communicate()
                    record["status"] = "timeout"
                except BaseException:
                    process.kill()
                    process.communicate()
                    raise
                finally:
                    record["returncode"] = process.returncode
        except BaseException as error:
            record["status"] = "interrupted" if isinstance(error, KeyboardInterrupt) else "launch_error"
            record["error"] = f"{type(error).__name__}: {error}"
            if isinstance(error, KeyboardInterrupt):
                self.cancel()
        finally:
            with self.lock:
                self.active.discard(process)
            record["ended_utc"] = now()
            record["elapsed_seconds"] = round(time.monotonic() - start, 6)
            stdout = (self.output / record["stdout_file"]).read_text(encoding="utf-8", errors="replace")
            stderr = (self.output / record["stderr_file"]).read_text(encoding="utf-8", errors="replace")
            record["output_check"] = output_check(kind, argument, stdout, stderr)
            record["passed"] = (record["status"] == "completed" and record["returncode"] == 0
                                and record["output_check"]["passed"])
            write_json(result_path, record)
        print(f"{name}: {'PASS' if record['passed'] else 'FAIL'} ({record['elapsed_seconds']:.2f}s)", flush=True)
        return record


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--output-dir", type=Path, required=True, help="new directory outside verification/")
    parser.add_argument("--compiler", default="g++", help="C++ compiler executable (default: g++)")
    parser.add_argument("--jobs", type=int, default=1, help="concurrent certificate processes (default: 1)")
    parser.add_argument("--timeout", type=float, default=1800, help="seconds allowed per process (default: 1800)")
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    output = args.output_dir.resolve()
    if output == source or source in output.parents:
        parser.error("--output-dir must be outside the certificate source directory")
    if args.jobs < 1 or not (0 < args.timeout < float("inf")):
        parser.error("--jobs and --timeout must be positive finite values")
    try:
        output.mkdir(parents=True, exist_ok=False)
    except OSError as error:
        parser.error(f"cannot create new --output-dir: {error}")
    replay = Replay(output, args.timeout)
    summary = {"schema_version": 1, "started_utc": now(), "status": "running", "passed": False,
               "source_directory": str(source), "output_directory": str(output),
               "runner_sha256": digest(Path(__file__).resolve()),
               "python": sys.version, "python_executable": sys.executable,
               "platform": platform.platform(), "machine": platform.machine(),
               "python_assertions_enabled": __debug__, "python_optimize_flag": sys.flags.optimize,
               "pythonoptimize_environment": os.environ.get("PYTHONOPTIMIZE"),
               "compile_flags": list(COMPILE_FLAGS), "jobs": args.jobs, "timeout_seconds": args.timeout,
               "expected_interval_visits": list(INTERVAL_VISITS), "expected_grid_iterations": GRID_ITERATIONS,
               "sources": {}, "processes": [], "skipped": []}
    summary_path = output / "summary.json"
    write_json(summary_path, summary)
    def run(*positional, **keywords):
        result = replay.run(*positional, **keywords)
        summary["processes"].append(result)
        write_json(summary_path, summary)
        return result
    try:
        if not __debug__:
            raise RuntimeError("Python assertions are disabled; run without -O/-OO or PYTHONOPTIMIZE")
        for name, expected in SOURCE_SHA256.items():
            actual = digest(source / name)
            summary["sources"][name] = {"sha256": actual, "expected_sha256": expected, "passed": actual == expected}
        write_json(summary_path, summary)
        if not all(item["passed"] for item in summary["sources"].values()):
            raise RuntimeError("certificate source SHA-256 mismatch")
        compiler = shutil.which(args.compiler)
        if compiler is None:
            raise RuntimeError(f"compiler not found: {args.compiler}")
        compiler = str(Path(compiler).resolve())
        python = [sys.executable, "-E", "-B"]
        probe = "import json,sys,sympy; print(json.dumps({'assertions_enabled': __debug__, 'python': sys.version, 'sympy_version': sympy.__version__, 'sympy_path': sympy.__file__}))"
        required = [
            run("python-environment", python + ["-c", probe], kind="python_probe"),
            run("compiler-version", [compiler, "--version"]),
            run("compiler-macros", [compiler, *COMPILE_FLAGS, "-dM", "-E", "-x", "c++", "-"],
                kind="compiler_macros", stdin=b"#include <cassert>\n"),
        ]
        if not all(item["passed"] for item in required):
            raise RuntimeError("environment or compiler preflight failed; inspect retained logs")
        binaries = {}
        for stem in ("interval", "grid"):
            binary = output / (stem + (".exe" if os.name == "nt" else ""))
            result = run("compile-" + stem, [compiler, *COMPILE_FLAGS, str(source / (stem + ".cpp")), "-o", str(binary)])
            if result["passed"] and binary.is_file():
                binaries[stem] = str(binary)
                result["binary_sha256"] = digest(binary)
                write_json(output / (result["name"] + ".json"), result)
            else:
                summary["skipped"].append({"certificate": stem, "reason": "compilation failed"})
        tasks = [("pair", python + [str(source / "pair.py")], "pair", None)]
        if "interval" in binaries:
            tasks.extend((f"interval-{i}", [binaries["interval"], str(i)], "interval", i) for i in range(3))
        if "grid" in binaries:
            tasks.extend((f"grid-{i}", [binaries["grid"], str(i)], "grid", i) for i in range(-1, 27))
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
            futures = [executor.submit(replay.run, name, command, kind, argument) for name, command, kind, argument in tasks]
            try:
                for future in concurrent.futures.as_completed(futures):
                    summary["processes"].append(future.result())
                    write_json(summary_path, summary)
            except BaseException:
                replay.cancel()
                for future in futures:
                    future.cancel()
                raise
        for name, item in summary["sources"].items():
            item["final_sha256"] = digest(source / name)
            item["passed"] = item["passed"] and item["final_sha256"] == item["expected_sha256"]
        summary["passed"] = (len(tasks) == 32 and len(summary["processes"]) == 37 and not summary["skipped"]
                             and all(item["passed"] for item in summary["sources"].values())
                             and all(item["passed"] for item in summary["processes"]))
        summary["status"] = "completed"
    except BaseException as error:
        replay.cancel()
        summary["status"] = "interrupted" if isinstance(error, KeyboardInterrupt) else "failed"
        summary["error"] = f"{type(error).__name__}: {error}"
        print(summary["error"], file=sys.stderr)
    finally:
        summary["ended_utc"] = now()
        write_json(summary_path, summary)
    print(f"{'PASS' if summary['passed'] else 'FAIL'}: {summary_path}", flush=True)
    return 0 if summary["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
