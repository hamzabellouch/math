#!/usr/bin/env python3
"""Reproduce the finite computations in a fresh directory; see computations/README.md."""
import argparse
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time

# An assertion cannot enforce this gate: python -O would remove the assertion.
if not __debug__ or sys.flags.optimize or os.environ.get("PYTHONOPTIMIZE", "0") not in ("", "0"):
    raise SystemExit("Verification requires assertions enabled. Remove -O/-OO and PYTHONOPTIMIZE.")

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "computations"
EVIDENCE = SOURCE / "evidence"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def read_json(path):
    return json.loads(path.read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rational(value):
    if isinstance(value, dict):
        return Fraction(value["numerator"], value["denominator"])
    return Fraction(value)


def check_source1(records, expected):
    require(records == expected, "Source1 exact thermal certificates differ from the reviewed values.")
    for row in records:
        center, lower, upper = map(rational, (row["center"], row["lower"], row["upper"]))
        error = Fraction(30, 10**6)
        require(center - error < lower <= upper < center + error, "Source1 thermal interval failed.")
        require(lower - (center-error) > Fraction(13, 10**6), "Source1 lower margin failed.")
        require(center+error-upper > Fraction(13, 10**6), "Source1 upper margin failed.")


def check_source2(actual, expected):
    fields = ("n", "twist", "total", "center", "computed_trace_lower", "computed_trace_upper",
              "scaled_frobenius_error_bound", "trace_error_bound", "true_trace_lower", "true_trace_upper")
    require(all(actual[k] == expected[k] for k in fields), "Source2 exact total or rational enclosure differs.")
    center = rational(actual["center"])
    lower, upper = map(rational, (actual["true_trace_lower"], actual["true_trace_upper"]))
    require(center-Fraction(1, 10**5) < lower <= upper < center+Fraction(1, 10**5),
            "Source2 true physical trace interval failed.")


def trial_values(record):
    num = int(next(record[k] for k in ("num", "one_bond_energy_numerator", "U") if k in record))
    norm = int(next(record[k] for k in ("norm", "V") if k in record))
    return num, norm


def check_trial(record, expected, length):
    num, norm = trial_values(record)
    require(record["length"] == expected["length"] == length, "Trial certificate length differs.")
    require((num, norm) == trial_values(expected), f"Trial {length} full integers differ.")
    require(norm > 0 and 500000*num < -700741*norm, f"Trial {length} variational inequality failed.")
    floor = {72: -1401482112601, 120: -1401482105174}[length]
    require(10**12*num // norm == floor, f"Trial {length} exact energy window failed.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "build" / "verification",
                        help="new output directory (must not already exist)")
    parser.add_argument("--only", choices=("all", "thermal1", "thermal2", "trial72", "trial120", "scalars", "smoke"),
                        default="all", help="all recomputes every required finite input; smoke runs source1 n=4 and scalars")
    parser.add_argument("--workers", type=int, default=8, help="source1 thermal worker processes")
    args = parser.parse_args()
    require(args.workers >= 1, "--workers must be positive.")
    out = args.output.resolve()
    require(out != SOURCE and SOURCE not in out.parents, "The output must be outside immutable computations/.")
    require(not out.exists(), f"Output already exists: {out}. Choose a fresh --output directory.")

    manifest = read_json(SOURCE / "source-manifest.json")
    require(digest(Path(__file__)) == manifest["verify_py_sha256"], "verify.py differs from its source manifest.")
    for name, sha in manifest["files"].items():
        require(digest(SOURCE / name) == sha, f"Source or evidence hash mismatch: {name}")
    out.mkdir(parents=True)
    for name in manifest["runtime_files"]:
        target = out / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(SOURCE / name, target)
    (out / "source2" / "runs").mkdir(exist_ok=True)
    logdir = out / "logs"
    logdir.mkdir()
    env = os.environ.copy()
    env.pop("PYTHONOPTIMIZE", None)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env["PYTHONHASHSEED"] = "0"
    summary = {"started_utc": datetime.now(timezone.utc).isoformat(), "selection": args.only,
               "full_recomputation": args.only == "all", "assertions_enabled": True,
               "python": platform.python_version(), "platform": platform.platform(),
               "numpy": importlib.metadata.version("numpy"), "scipy": importlib.metadata.version("scipy"),
               "workers": args.workers, "source_manifest_sha256": digest(SOURCE / "source-manifest.json"),
               "commands": [], "checks": []}

    def run(directory, script, *options, log=None):
        command = [sys.executable, "-u", script, *map(str, options)]
        logfile = logdir / (log or script.replace(".py", ".log"))
        print("Running", directory, script, *options, flush=True)
        started = time.monotonic()
        with logfile.open("w") as stream:
            completed = subprocess.run(command, cwd=out/directory, env=env, stdout=stream, stderr=subprocess.STDOUT)
        summary["commands"].append({"cwd": directory, "command": command, "log": str(logfile.relative_to(out)),
                                    "seconds": time.monotonic()-started, "exit_code": completed.returncode})
        require(completed.returncode == 0, f"Command failed; see {logfile}")
        return logfile

    selected = args.only
    try:
        if selected in ("all", "thermal1", "smoke"):
            run("source1", "run_thermal.py", "--workers", args.workers, "--max-n", 4 if selected == "smoke" else 12,
                log="thermal1.log")
            actual = read_json(out / "source1/thermal-run/certificates.json")
            expected = read_json(EVIDENCE / "source1/thermal-run/certificates.json")
            if selected == "smoke":
                expected = [row for row in expected if row["n"] == 4]
            check_source1(actual, expected)
            text = "".join(f'{r["n"]} {r["tw"]} {r["W"]}\n' for r in actual)
            require((out/"source1/thermal-run/outputs.txt").read_text() == text, "Source1 output table mismatch.")
            summary["checks"].append(f"source1: {len(actual)} newly computed exact totals and full rational intervals")

        if selected in ("all", "thermal2"):
            for twist in range(3):
                run("source2", "run_thermal.py", "--twist", twist, log=f"thermal2-twist{twist}.log")
            totals = []
            for n in (6, 8, 10):
                for twist in range(3):
                    name = f"source2/runs/n{n}-g{twist}.json"
                    actual = read_json(out/name)
                    check_source2(actual, read_json(EVIDENCE/name))
                    totals.append(str(actual["total"]))
            text = "\n".join(totals)+"\n"
            require(text == (SOURCE/"source2/thermal-expected.txt").read_text(), "Source2 output table mismatch.")
            (out/"source2/runs/thermal-actual.txt").write_text(text)
            summary["checks"].append("source2: all nine newly computed exact totals and error-expanded rational intervals")

        if selected in ("all", "trial72", "trial120"):
            lengths = (72, 120) if selected == "all" else (int(selected[5:]),)
            for length in lengths:
                run("trials", "run_trial.py", "--length", length, log=f"trial{length}.log")
                check_trial(read_json(out/f"trials/certificate{length}.json"),
                            read_json(EVIDENCE/f"trials/certificate{length}.json"), length)
                # Compare matrices captured from each full executed contraction,
                # before a separate small-chain checker regenerates them.
                require(read_json(out/"trials/matrix-data.json") == read_json(EVIDENCE/"trials/matrix-data.json"),
                        f"Trial {length} did not use the common polynomial matrices.")
                summary["checks"].append(f"trial{length}: fresh full norm/energy, exact variational window and common matrix triple")
            run("trials", "exact_checks.py", log="trial-small-chain.log")
            require(read_json(out/"trials/matrix-data.json") == read_json(EVIDENCE/"trials/matrix-data.json"),
                    "Small-chain check matrix entries differ.")
            summary["checks"].append("one shared trial matrix triple: all entries and four-site physical contraction")

        if selected in ("all", "scalars", "smoke"):
            run("source1", "check_error_bounds.py", log="thermal1-error-bounds.log")
            run("source1", "check_symmetry.py", log="thermal1-symmetry.log")
            run("source1", "run_initialization.py", log="source1-original-initialization.log")
            run("source2", "initialization.py", log="source2-original-initialization.log")
            run("source2", "audit_arithmetic.py", log="thermal2-arithmetic.log")
            run("source2", "packed_lanes_independent_check.py", log="thermal2-packed-lanes.log")
            run("scalars", "check-moment-initializations.py", log="moment-initializations.log")
            run("scalars", "check-bootstrap-scalars.py", log="bootstrap-scalars.log")
            if selected != "all":
                for name in ("certificate72.json", "certificate120.json", "matrix-data.json"):
                    shutil.copyfile(EVIDENCE/f"trials/{name}", out/f"trials/{name}")
            run("trials", "verify_entry_recipe.py", log="trial-entry-recipe.log")
            run("trials", "check_certificate_windows.py", log="trial-energy-windows.log")
            expected_rounds = (SOURCE/"source1/source-output.txt").read_text().splitlines()[-6:]
            require((logdir/"source1-original-initialization.log").read_text().splitlines() == expected_rounds,
                    "Original source1 rounded scalar iterations differ.")
            # In a partial run these check the retained evidence, not newly
            # calculated full thermal matrices or trial contractions.
            certs = read_json(EVIDENCE/"source1/thermal-run/certificates.json")
            check_source1(certs, certs)
            for n in (6, 8, 10):
                for twist in range(3):
                    record = read_json(EVIDENCE/f"source2/runs/n{n}-g{twist}.json")
                    check_source2(record, record)
            summary["checks"].append("all exact scalar, rounding, packing, initialization and manuscript entry/window checks")
            if selected != "all":
                summary["checks"].append("remaining full thermal/trial records checked as frozen evidence only")
        summary["success"] = True
    except BaseException as error:
        summary["success"] = False
        summary["error"] = str(error)
        raise
    finally:
        summary["finished_utc"] = datetime.now(timezone.utc).isoformat()
        (out/"verification.json").write_text(json.dumps(summary, indent=2)+"\n")
    print("PASS:", selected, "verification; evidence in", out, flush=True)


if __name__ == "__main__":
    main()
