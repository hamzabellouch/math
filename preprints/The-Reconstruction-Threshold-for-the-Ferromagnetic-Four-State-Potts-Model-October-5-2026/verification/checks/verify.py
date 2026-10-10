#!/usr/bin/env python3
"""Lightweight checks; validate, but do not repeat, the full sign traversals."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
CHECKS = ROOT / "checks"
SOURCE_HASH = "9f9765fb4dee9f2fc618390df89d3abccf2602569709fd4c2133a201b6e86bff"
SOURCE_INPUT_HASH = "995953790608f7214e882dcd9fe42e47b254bb44500a1e18eafbf067293bff4f"
EXPECTED = {
    "a": "done 4479 19 lp=2074 lt=166",
    "b": "done 1935 20 lp=871 lt=97",
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def run(command, logfile, env):
    result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True)
    logfile.write_text(result.stdout + result.stderr)
    require(result.returncode == 0, f"Command failed: {command}; see {logfile}")
    return result.stdout


def output_directory(requested):
    path = requested if requested.is_absolute() else ROOT / requested
    path = Path(os.path.abspath(path))
    require(path.is_relative_to(ROOT / "artifacts"),
            "Generated output must stay under this bundle's artifacts directory")
    current = ROOT
    for part in path.relative_to(ROOT).parts:
        current = current / part
        require(not current.is_symlink(), f"Symlinked output path: {current}")
        require(not current.exists() or current.is_dir(),
                f"Output parent is not a directory: {current}")
    if path.exists():
        for entry in path.rglob("*"):
            require(not entry.is_symlink(), f"Symlinked generated file: {entry}")
    path.mkdir(parents=True, exist_ok=True)
    return path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-dir", type=Path, default=ROOT / "artifacts" / "checks")
    args = parser.parse_args()
    output = output_directory(args.build_dir)

    source_input = (CHECKS / "certificate-source.txt").read_bytes()
    source = (CHECKS / "certificate.cpp").read_bytes()
    require(digest(source_input) == SOURCE_INPUT_HASH, "Certificate source input hash mismatch")
    require(digest(source) == SOURCE_HASH, "Certificate source hash mismatch")
    lines = source_input.splitlines(keepends=True)
    start = next(i for i, line in enumerate(lines) if line.startswith(b"    #include<bits"))
    extracted = b"".join(line[4:] for line in lines[start:] if line.startswith(b"    "))
    require(extracted == source, "Certificate is not the literal source extraction")
    print("Exact source-input-to-C++ extraction and source hashes: PASS")

    env = dict(os.environ)
    env.pop("PYTHONOPTIMIZE", None)
    scalar = json.loads(run(
        [sys.executable, str(CHECKS / "small_polynomials.py")],
        output / "scalar.log", env,
    ))
    minima = {item["name"]: item["minimum"] for item in scalar["small_checks"]}
    require(minima == {
        "H+1/2": "19/50", "F": "0", "G": "87/1000", "(3-Euler)H": "0"
    }, "Scalar coefficient minima mismatch")
    require(scalar["all_24_symmetry_actions_verified"], "Symmetry check failed")
    print("Four exact scalar minima and 24 symmetry actions: PASS")

    binary = output / "safety-unit"
    compile_command = [
        "g++", "-std=c++17", "-O2", "-UNDEBUG", "-fsanitize=undefined",
        "-fno-sanitize-recover=all", str(CHECKS / "safety-unit.cpp"), "-o", str(binary),
    ]
    run(compile_command, output / "safety-build.log", env)
    safety = run([str(binary)], output / "safety-unit.log", env)
    require("All focused exactness and safety assertions passed." in safety,
            "Safety harness did not report success")
    print("Focused exact arithmetic/interpolation/subdivision checks under UBSan: PASS")

    recorded = json.loads((CHECKS / "full-runs.json").read_text())
    require(recorded["source_sha256"] == SOURCE_HASH, "Full-run source binding mismatch")
    full_runs = []
    for mode, marker in EXPECTED.items():
        item = recorded["runs"][mode]
        log = CHECKS / "logs" / f"paper-mode-{mode}.log"
        data = log.read_bytes()
        require(item["exit_code"] == 0 and item["assertions_enabled"],
                f"Mode {mode} was not successfully checked with assertions")
        require(digest(data) == item["log_sha256"], f"Mode {mode} log hash mismatch")
        final = [line for line in data.decode().splitlines() if line.startswith("done ")]
        require(final == [marker], f"Mode {mode} completion counts mismatch")
        full_runs.append({"mode": mode, "marker": marker, "log_sha256": digest(data)})
        print(f"Recorded full sign check {mode}, source/log binding: {marker}")

    receipt = {
        "scope": "Lightweight rechecks and validation of previously completed full exact sign runs",
        "full_sign_runs_repeated": False,
        "source_input_sha256": SOURCE_INPUT_HASH,
        "certificate_sha256": SOURCE_HASH,
        "scalar_minima": minima,
        "all_24_symmetry_actions_verified": True,
        "focused_ubsan_checks_passed": True,
        "recorded_full_runs": full_runs,
    }
    (output / "verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print("Full traversals were not repeated; receipt: artifacts/checks/verification.json")


if __name__ == "__main__":
    main()
