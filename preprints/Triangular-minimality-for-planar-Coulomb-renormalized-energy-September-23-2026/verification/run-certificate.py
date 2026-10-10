#!/usr/bin/env python3
"""Compile and run the exact scalar certificate with a source-bound receipt."""

import argparse
import datetime
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import subprocess
import time


SOURCES = ("certificate.cpp", "core.hpp", "grids.hpp", "run-certificate.py")
STAGES = (
    "init_core including core_test",
    "calcLam",
    "calcK",
    "bdsup",
    "global_grid",
    "inside_hess",
)
MESH_LINES = (
    "MESH bdsup 519 x 813",
    "MESH global_grid 2186 x 3612",
    "MESH inside_hess 601 x 4079",
)


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_hashes(source_dir):
    return {name: sha256(source_dir / name) for name in SOURCES}


def validate_run_log(text):
    """Require every fixed stage, in order, before accepting terminal OK."""
    lines = text.splitlines()
    errors = []
    header = re.fullmatch(
        r"CERTIFICATE BP=144 M=38 BOOST=(\S+) OMP_MAX_THREADS=32",
        lines[0] if lines else "",
    )
    if header is None:
        errors.append("missing or unexpected certificate/toolchain header")
    events = []
    timings = {}
    for line in lines:
        if line.startswith("BEGIN "):
            events.append(("BEGIN", line[6:]))
        elif line.startswith("TIMING "):
            match = re.fullmatch(r"TIMING (.+) ([0-9.eE+-]+) seconds", line)
            if match is None:
                errors.append("malformed timing line")
                continue
            label, value = match.groups()
            elapsed = float(value)
            if not math.isfinite(elapsed) or elapsed < 0:
                errors.append("invalid elapsed time")
            events.append(("TIMING", label))
            timings[label] = elapsed
        elif line == "OK":
            events.append(("OK", ""))
        elif line.startswith("CERTIFICATE ERROR:"):
            errors.append(line)
    expected = [("BEGIN", "full certificate")]
    for stage in STAGES:
        expected.extend((("BEGIN", stage), ("TIMING", stage)))
    expected.extend((("OK", ""), ("TIMING", "full certificate")))
    if events != expected:
        errors.append("missing, duplicated, reordered, or unexpected certificate stage")
    for marker in MESH_LINES:
        if lines.count(marker) != 1:
            errors.append("missing or duplicated mesh marker: " + marker)
    if not lines or not lines[-1].startswith("TIMING full certificate "):
        errors.append("certificate output does not end after full-certificate timing")
    return {
        "passed": not errors,
        "errors": errors,
        "events": events,
        "timings_seconds": timings,
        "boost_version": header.group(1) if header else None,
        "expected_mesh_markers": list(MESH_LINES),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        help="directory for the executable, logs, and receipt (default: certificate-run beside this script)",
    )
    args = parser.parse_args()
    source_dir = Path(__file__).resolve().parent
    output_dir = (args.output_dir or source_dir / "certificate-run").resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    executable = output_dir / "certificate"
    compile_log = output_dir / "compile.log"
    run_log = output_dir / "run.log"
    receipt_path = output_dir / "run-receipt.json"
    command = [
        "g++", "-std=c++17", "-O3", "-fopenmp",
        str(source_dir / "certificate.cpp"), "-o", str(executable),
    ]
    receipt = {
        "start_utc": utc(),
        "source_directory": str(source_dir),
        "output_directory": str(output_dir),
        "source_sha256_before": source_hashes(source_dir),
        "compile_command": command,
        "compile_cwd": str(output_dir),
        "python": platform.python_version(),
        "platform": platform.platform(),
        "assertions": "active; source rejects NDEBUG",
        "precision_bits": 144,
        "modes": 38,
    }
    started = time.monotonic()
    status = 1
    try:
        version = subprocess.run(
            ["g++", "--version"], capture_output=True, text=True, check=True,
        )
        receipt["compiler"] = version.stdout.splitlines()[0]
        with compile_log.open("w") as log:
            built = subprocess.run(
                command, cwd=output_dir, stdout=log, stderr=subprocess.STDOUT,
            )
        receipt["compile_exit_status"] = built.returncode
        receipt["compile_log_sha256"] = sha256(compile_log)
        status = built.returncode
        if built.returncode == 0:
            receipt["executable_sha256"] = sha256(executable)
            env = os.environ.copy()
            env["OMP_NUM_THREADS"] = "32"
            receipt["environment"] = {"OMP_NUM_THREADS": "32"}
            receipt["run_command"] = [str(executable)]
            receipt["run_cwd"] = str(output_dir)
            receipt["run_start_utc"] = utc()
            print("Starting full certificate", receipt["run_start_utc"], flush=True)
            with run_log.open("w") as log:
                result = subprocess.run(
                    [str(executable)], cwd=output_dir, env=env,
                    stdout=log, stderr=subprocess.STDOUT,
                )
            receipt["exit_status"] = result.returncode
            receipt["log_sha256"] = sha256(run_log)
            receipt["stage_validation"] = validate_run_log(run_log.read_text())
            receipt["terminal_OK"] = receipt["stage_validation"]["passed"]
            status = result.returncode or (0 if receipt["terminal_OK"] else 1)
    except (OSError, subprocess.SubprocessError, ValueError) as error:
        receipt["error"] = str(error)
        status = 1
    receipt["end_utc"] = utc()
    receipt["elapsed_seconds"] = time.monotonic() - started
    receipt["source_sha256_after"] = source_hashes(source_dir)
    receipt["sources_unchanged"] = (
        receipt["source_sha256_before"] == receipt["source_sha256_after"]
    )
    if not receipt["sources_unchanged"]:
        status = status or 1
    receipt["wrapper_exit_status"] = status
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2), flush=True)
    return status


if __name__ == "__main__":
    raise SystemExit(main())
