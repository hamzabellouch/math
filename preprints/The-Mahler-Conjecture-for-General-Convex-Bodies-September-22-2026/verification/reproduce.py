#!/usr/bin/env python3
"""Run the unchanged source certificates in a new, isolated directory.

The saved-original results are comparison material, never input. The scalar
node file used by the segment program is generated afresh by the first command.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time

BASE = Path(__file__).resolve().parent
COMMANDS = [
    "scalar_intervals.py",
    "scalar_algebra.py",
    "scalar_identities.py",
    "scalar-analytic.py",
    "interpolation-check.py",
    "segment-auxiliary-intervals.py",
    "segment-middle-polynomials.py",
    "segment-middle-r-certificate.py",
    "segment-large-check.py",
    "segment-large-tail-audit.py",
]
RESULTS = {
    "scalar_intervals.py": "scalar-interval-results.json",
    "scalar_algebra.py": "scalar-algebra-results.json",
    "scalar_identities.py": "scalar-identity-results.json",
    "segment-auxiliary-intervals.py": "segment-auxiliary-interval-results.json",
    "segment-middle-polynomials.py": "segment-middle-polynomials-results.json",
}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_report(program, data):
    """Some inherited programs report failure without a nonzero exit code."""
    if "failed" in data:
        flag = "passed" if program == "segment-auxiliary-intervals.py" else "pass"
        return data["failed"] == 0 and all(c[flag] for c in data["checks"])
    if program == "scalar_identities.py":
        return len(data) == 3 and all(v is True for v in data.values())
    if program == "segment-middle-polynomials.py":
        return all(data[p]["all_positive"] and
                   all(g["claim_true"] for g in data[p]["groups"])
                   for p in ("T4", "T5")) and all(
                       data["Pu_tail"][k] for k in
                       ("index8_claim_true", "allowance_sufficient"))
    raise ValueError(f"No result validator for {program}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True,
                        help="New directory; refusing to overwrite an existing run")
    args = parser.parse_args()
    if sys.flags.optimize:
        parser.error("Run without -O: inherited certificates use assertions")
    import sympy
    target = args.output.resolve()
    target.mkdir(parents=True, exist_ok=False)
    programs = sorted((BASE / "programs").glob("*.py"))
    manifest = json.loads((BASE / "SOURCE-MANIFEST.json").read_text())
    for source in programs:
        if sha256(source) != manifest["source_files"][source.name]:
            raise RuntimeError(f"Program differs from pinned source: {source.name}")
        shutil.copy2(source, target / source.name)
    record = {
        "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "python": sys.version,
        "python_executable": sys.executable,
        "python_optimization": sys.flags.optimize,
        "platform": platform.platform(),
        "dependencies": {"sympy": sympy.__version__},
        "input_program_sha256": {p.name: sha256(p) for p in programs},
        "input_policy": "Only programs copied; no saved results or node data copied",
        "source_manifest_sha256": sha256(BASE / "SOURCE-MANIFEST.json"),
        "steps": [],
    }
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    # Import only the copied, hash-checked local arithmetic helpers.
    env["PYTHONPATH"] = str(target)
    env.pop("PYTHONOPTIMIZE", None)
    success = True
    for program in COMMANDS:
        argv = [sys.executable, program]
        start = time.perf_counter()
        with (target / (program + ".stdout.txt")).open("w") as stdout, \
             (target / (program + ".stderr.txt")).open("w") as stderr:
            result = subprocess.run(argv, cwd=target, env=env,
                                    stdout=stdout, stderr=stderr)
        elapsed = time.perf_counter() - start
        passed = result.returncode == 0
        report = RESULTS.get(program)
        if passed and report:
            passed = check_report(program, json.loads((target / report).read_text()))
        step = {"command": argv, "elapsed_seconds": round(elapsed, 6),
                "returncode": result.returncode, "passed": passed}
        if report and (target / report).exists():
            step["report"] = report
            step["report_sha256"] = sha256(target / report)
            original = BASE / "saved-original" / report
            step["matches_saved_original_bytes"] = (
                original.exists() and sha256(original) == sha256(target / report))
        record["steps"].append(step)
        print(f"{'PASS' if passed else 'FAIL'} {program} ({elapsed:.3f}s)", flush=True)
        if not passed:
            success = False
            break
    record["passed"] = success and len(record["steps"]) == len(COMMANDS)
    record["finished_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    record["outputs_sha256"] = {
        p.name: sha256(p) for p in sorted(target.iterdir())
        if p.is_file() and p.suffix != ".py"
    }
    (target / "RUN.json").write_text(json.dumps(record, indent=2) + "\n")
    return 0 if record["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
