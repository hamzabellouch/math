#!/usr/bin/env python3
"""Compile and execute the complete portable exact-arithmetic certificate bundle."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import shlex
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parent
SOURCES = (
    "interval_certificate.cpp", "profile_certificate.py", "central_band.py",
    "intermediate_bias.py", "large_bias.py", "profile_formula_audit.py",
    "data/profile_tables.txt", "requirements.txt", "provenance.json",
    "README.md", "verify_all.py",
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        help="new or empty results directory (default: a new directory in cwd)")
    parser.add_argument("--cxx", default=os.environ.get("CXX", "c++"),
                        help="C++ compiler command (default: CXX or c++)")
    parser.add_argument("--timeout", type=float, default=1800,
                        help="maximum seconds per compilation/check (default: 1800)")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    if not shlex.split(args.cxx):
        parser.error("--cxx must be a compiler command")
    if args.output_dir is None:
        output = Path(tempfile.mkdtemp(prefix="certificate-results-", dir=Path.cwd()))
    else:
        output = args.output_dir.resolve()
        if output.exists() and any(output.iterdir()):
            parser.error("--output-dir must be new or empty; existing evidence is preserved")
        output.mkdir(parents=True, exist_ok=True)
    status_file = output / "verification.json"
    started = time.monotonic()
    report = {
        "status": "running",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "python_version": sys.version,
        "python_executable": sys.executable,
        "platform": platform.platform(),
        "source_sha256": {},
        "steps": [],
    }

    def save():
        report["wall_seconds"] = time.monotonic() - started
        status_file.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    def run(name, command, cwd, success_marker=None):
        print(f"RUN  {name}", flush=True)
        begin = time.monotonic()
        stdout = output / f"{name}.stdout.txt"
        stderr = output / f"{name}.stderr.txt"
        entry = {"name": name, "command": command,
                 "stdout": stdout.name, "stderr": stderr.name}
        try:
            with stdout.open("w", encoding="utf-8") as out, stderr.open("w", encoding="utf-8") as err:
                result = subprocess.run(command, cwd=cwd, stdout=out, stderr=err,
                                        timeout=args.timeout, check=False)
            entry["exit_code"] = result.returncode
            entry["success_marker"] = success_marker
            entry["success_marker_found"] = (
                success_marker is None or
                success_marker in stdout.read_text(encoding="utf-8").splitlines()
            )
            passed = result.returncode == 0 and entry["success_marker_found"]
            entry["status"] = "pass" if passed else "fail"
        except (OSError, subprocess.TimeoutExpired) as error:
            entry.update(status="fail", error=str(error))
            passed = False
        entry["wall_seconds"] = time.monotonic() - begin
        report["steps"].append(entry)
        save()
        print(f"{'PASS' if passed else 'FAIL'} {name} ({entry['wall_seconds']:.2f}s)", flush=True)
        return passed

    try:
        report["source_sha256"] = {
            name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            for name in SOURCES
        }
        save()
        with tempfile.TemporaryDirectory(prefix="hellinger-certificate-build-") as build_name:
            build = Path(build_name)
            compiler = shlex.split(args.cxx)
            # -I ignores PYTHONOPTIMIZE and user site/customization. Assertions in
            # the independent checks remain enabled, even if this runner used -O.
            python = [sys.executable, "-I"]
            dependency_check = (
                "import json,sys,sympy; "
                "print(json.dumps({'python':sys.version,'sympy':sympy.__version__,"
                "'assertions_enabled':__debug__})); "
                "assert __debug__; assert sympy.__version__ == '1.14.0'; print('pass')"
            )
            checks = [
                ("environment", python + ["-c", dependency_check], "pass"),
                ("compiler_version", compiler + ["--version"], None),
                ("compile_interval", compiler + ["-O2", "-std=gnu++17",
                 str(ROOT / "interval_certificate.cpp"), "-o", str(build / "interval_certificate")], None),
                ("interval_certificate", [str(build / "interval_certificate")], "pass"),
                ("profile_certificate", python + [str(ROOT / "profile_certificate.py")], "pass"),
                ("profile_formula_audit", python + [str(ROOT / "profile_formula_audit.py"),
                 "--output", str(output / "profile_formula_audit.results.json")], "pass"),
                ("central_band", python + [str(ROOT / "central_band.py")],
                 "PASS: central exact certificates and rational constant bounds"),
                ("intermediate_bias", python + [str(ROOT / "intermediate_bias.py")],
                 "PASS: rational root-coefficient and middle-band scalar margins"),
                ("large_bias", python + [str(ROOT / "large_bias.py")],
                 "PASS: all four claimed upward-rounded constants reproduced with exact rational arithmetic"),
            ]
            for name, command, marker in checks:
                if not run(name, command, build, marker):
                    report["status"] = "fail"
                    break
            else:
                report["status"] = "pass"
    except (OSError, ValueError) as error:
        report.update(status="fail", error=str(error))
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    save()
    print(f"{report['status'].upper()}: results in {output}", flush=True)
    return 0 if report["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
