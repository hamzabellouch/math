#!/usr/bin/env python3
"""Test relocation and selected rejection paths without third-party packages.

Author: OpenAI. All temporary output stays inside this package directory.
"""
import sys
sys.dont_write_bytecode = True
import hashlib
import json
from pathlib import Path
import platform
import shutil
import subprocess
import tempfile

from polynomial import Poly, interval_coefficients, require, ring, triangle_coefficients

ROOT = Path(__file__).resolve().parent
RUNTIME_FILES = ("verify.py", "polynomial.py", "results.json")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    checks = []
    originals = {name: sha(ROOT / name) for name in RUNTIME_FILES}
    with tempfile.TemporaryDirectory(prefix=".portability-", dir=ROOT) as temporary:
        base = Path(temporary)
        package, other_cwd = base / "relocated-package", base / "different-cwd"
        package.mkdir()
        other_cwd.mkdir()
        for name in RUNTIME_FILES:
            shutil.copyfile(ROOT / name, package / name)
        command = [sys.executable, "-B", str(package / "verify.py"), "--check"]
        run = subprocess.run(command, cwd=other_cwd, capture_output=True, text=True, check=False)
        require(run.returncode == 0, "Relocated verification failed: " + run.stderr)
        require({name: sha(package / name) for name in RUNTIME_FILES} == originals,
                "Read-only --check changed the runtime files")
        checks.append({"name": "relocated_run_from_different_cwd", "passed": True,
                       "command": "python -B ../relocated-package/verify.py --check",
                       "stdout": run.stdout.splitlines()})
        # Ensure optimized Python does not disable assertions.
        optimized = subprocess.run([sys.executable, "-O", "-B", str(package / "verify.py"), "--check"],
                                   cwd=other_cwd, capture_output=True, text=True, check=False)
        require(optimized.returncode == 0, "Optimized interpreter verification failed")
        checks.append({"name": "optimized_python_checks_remain_active", "passed": True})
        results = package / "results.json"
        pristine_results = results.read_bytes()
        results.write_bytes(pristine_results + b" ")
        modified = subprocess.run(command, cwd=other_cwd, capture_output=True, text=True, check=False)
        require(modified.returncode != 0 and "differ from bundled" in modified.stderr,
                "Altered bundled results were not rejected")
        results.write_bytes(pristine_results)
        checks.append({"name": "altered_saved_results_rejected", "passed": True})
        verifier = package / "verify.py"
        pristine_verifier = verifier.read_text(encoding="utf-8")
        require("Q(11041, 810)" in pristine_verifier, "Printed triple mutation target missing")
        verifier.write_text(pristine_verifier.replace("Q(11041, 810)", "Q(11042, 810)", 1), encoding="utf-8")
        wrong_triple = subprocess.run([sys.executable, "-O", "-B", str(verifier), "--check"],
                                     cwd=other_cwd, capture_output=True, text=True, check=False)
        require(wrong_triple.returncode != 0 and "eq22.printed_CBE.8.0" in wrong_triple.stderr,
                "Incorrect printed CBE triple was not rejected")
        checks.append({"name": "incorrect_printed_triple_rejected_under_O", "passed": True})
        verifier.write_text(pristine_verifier, encoding="utf-8")
        mutations = [
            ("incorrect_zero_locations_rejected", "{(9, 1), (10, 0)}", "{(8, 1), (10, 0)}", "Exact zero pattern failed: eq22.B.CBE"),
            ("violated_coefficient_floor_rejected", "8, 16000, 53000000", "8, 20000, 53000000", "Matrix diagonal bound failed: eq21.A.OSC"),
        ]
        for name, old, new, expected_error in mutations:
            require(old in pristine_verifier, "Mutation target missing: " + name)
            verifier.write_text(pristine_verifier.replace(old, new, 1), encoding="utf-8")
            rejected = subprocess.run([sys.executable, "-O", "-B", str(verifier), "--check"],
                                      cwd=other_cwd, capture_output=True, text=True, check=False)
            require(rejected.returncode != 0 and expected_error in rejected.stderr,
                    "Invalid certificate was not rejected: " + name)
            checks.append({"name": name, "passed": True})
        verifier.write_text(pristine_verifier, encoding="utf-8")
    x, y = ring("x", "y")
    (u,) = ring("u")
    rejection_cases = [
        ("univariate_degree_truncation_rejected", lambda: interval_coefficients(u ** 3, 0, 1, 2)),
        ("triangle_degree_truncation_rejected", lambda: triangle_coefficients(x ** 3, [(0, 0), (1, 0), (0, 1)], 2)),
        ("inexact_polynomial_division_rejected", lambda: (u ** 2 + 1).divide_exact(u)),
        ("floating_point_coefficient_rejected", lambda: Poly.constant(("u",), 0.1)),
    ]
    for name, operation in rejection_cases:
        try:
            operation()
        except (ArithmeticError, TypeError):
            checks.append({"name": name, "passed": True})
        else:
            raise ArithmeticError("Rejection check unexpectedly succeeded: " + name)
    require({name: sha(ROOT / name) for name in RUNTIME_FILES} == originals,
            "Portability test changed the original runtime files")
    checks.append({"name": "original_runtime_files_unchanged", "passed": True})
    output = {"author": "OpenAI", "python_version": platform.python_version(),
              "third_party_dependencies": [], "network_used": False,
              "temporary_files_outside_package": False, "runtime_sha256": originals,
              "checks": checks, "all_passed": True}
    (ROOT / "portability-results.json").write_text(json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("PASS: relocation, read-only verification, and all rejection checks.")
    print(json.dumps({"checks": len(checks), "all_passed": True}, sort_keys=True))


if __name__ == "__main__":
    main()
