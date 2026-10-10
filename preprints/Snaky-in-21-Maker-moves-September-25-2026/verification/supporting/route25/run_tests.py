#!/usr/bin/env python3
"""Exercise both standalone certificate readers, including optimized Python."""
import argparse
import ast
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
CHECKERS = ["verify_certificate.py", "independent_certificate.py"]
COMPARE = ["literal_data_sha256", "numeric_rows_sha256", "cards", "numeric_rows",
           "placement_terms", "marker_count", "endpoint", "maximum_height",
           "required_cardinality_histogram_0_to_10",
           "all_2010_composition_normalizations_exact", "reduced_sets_heights_sha256",
           "full_sets_heights_sha256", "heights_sha256"]


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", "--evidence", dest="evidence", type=Path, help="save stdout/stderr and receipt here")
    args = parser.parse_args()
    if args.evidence:
        args.evidence = args.evidence.resolve()
        args.evidence.mkdir(parents=True, exist_ok=True)
    outcomes = []
    raw = (HERE / "certificate.txt").read_bytes()

    def run(checker, options, path, label, expected, script_options=()):
        command = [sys.executable, "-B"] + options + [str(HERE / checker), str(path), "--json"] + list(script_options)
        process = subprocess.run(command, capture_output=True, text=True, cwd=HERE)
        require((process.returncode == 0) == expected,
                "%s %s: expected success=%s; rc=%d; stderr=%r" %
                (checker, label, expected, process.returncode, process.stderr))
        if not expected:
            require("FAIL:" in process.stderr, "failure lacks explicit diagnostic")
            require("Traceback" not in process.stderr, "failure leaked an unhandled exception")
        if args.evidence:
            stem = checker.removesuffix(".py") + "." + label
            (args.evidence / (stem + ".stdout")).write_text(process.stdout)
            (args.evidence / (stem + ".stderr")).write_text(process.stderr)
        outcomes.append({"checker": checker, "test": label, "returncode": process.returncode,
                         "expected_success": expected, "stderr": process.stderr.strip()})
        return json.loads(process.stdout) if expected else None

    results = []
    for checker in CHECKERS:
        for mode in [[], ["-O"], ["-OO"]]:
            label = "canonical." + (mode[0][1:] if mode else "default")
            results.append(run(checker, mode, HERE / "certificate.txt", label, True))
    reference = {key: results[0][key] for key in COMPARE}
    require(all({key: result[key] for key in COMPARE} == reference for result in results),
            "independent checker or optimization-mode reconstruction disagrees")
    identity = json.loads((HERE / "identity.json").read_text())
    require(reference == identity["expected_reconstruction"], "reconstruction differs from identity manifest")
    for name, entry in identity["files"].items():
        payload = (HERE / name).read_bytes()
        require(len(payload) == entry["bytes"] and hashlib.sha256(payload).hexdigest() == entry["sha256"],
                "file identity mismatch: " + name)

    for name in CHECKERS + ["run_tests.py"]:
        tree = ast.parse((HERE / name).read_text(), filename=name)
        require(not any(isinstance(node, ast.Assert) for node in ast.walk(tree)),
                "optimization-dependent assert statement in " + name)
        outcomes.append({"checker": name, "test": "AST_no_assert_statements",
                         "returncode": 0, "expected_success": True})

    # The harness imports both implementations; neither implementation imports
    # the other. Compare the complete sets and heights, independently of their
    # serialization and digests. Prevent bytecode writes before these imports.
    implementations = []
    for name in CHECKERS:
        spec = importlib.util.spec_from_file_location(name.removesuffix(".py"), HERE / name)
        require(spec is not None and spec.loader is not None, "cannot load " + name)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        implementations.append(module)
    primary, independent = implementations
    unused_result, primary_reduced, unused_terms, primary_full = primary.reconstruct(raw)
    independent_rows, unused_numeric, unused_count = independent.read_rows(raw)
    independent_full, independent_reduced = independent.reconstruct(independent_rows)
    require(len(primary_reduced) == len(primary_full) == len(independent_reduced) ==
            len(independent_full) == 2016, "complete array length mismatch")
    for row in range(2016):
        require(primary_reduced[row] == independent_reduced[row],
                "direct reduced-card set/height mismatch at card %d" % row)
        require(primary_full[row] == independent_full[row],
                "direct full-card set/height mismatch at card %d" % row)
    outcomes.append({"checker": "both", "test": "all_2016_reduced_and_full_set_height_arrays_equal",
                     "returncode": 0, "expected_success": True})

    # Each malformed fixture has one specified defect. --allow-noncanonical is
    # appended to the script arguments so these reach structural validation.
    variants = {
        "empty": b"",
        "partial_triple": raw.replace(b"193233", b"19323", 1),
        "truncated_extended": raw.replace(b"193233", b"740", 1),
        "forward_reference": raw.replace(b"193233", b"740600", 1),
        "out_of_range_anchor": raw.replace(b"193233", b"740099", 1),
        "non_ascii_digit": raw.replace(b"193233", "١93233".encode(), 1),
        "nondigit": raw.replace(b"193233", b"19x233", 1),
        "changed_geometry": raw.replace(b"193233", b"192233", 1),
        "wrong_marker": raw.replace(b"# 6\n", b"# 7\n", 1),
        "malformed_marker": raw.replace(b"# 6\n", b"# 6 trailing\n", 1),
        "duplicate_marker": raw.replace(b"# 6\n", b"# 6\n# 6\n", 1),
        "missing_marker": raw.replace(b"# 6\n", b"", 1),
        "truncated_rows": raw[:raw.rfind(b"\n", 0, len(raw)-1)+1],
        "extra_row": raw + b"000\n",
    }
    with tempfile.TemporaryDirectory(prefix="route25-tests-", dir=args.evidence) as folder:
        root = Path(folder)
        for label, payload in variants.items():
            path = root / (label + ".txt")
            path.write_bytes(payload)
            for checker in CHECKERS:
                # Positioning this flag after the script is independent of the
                # Python -O option. All malformed cases are tested under -O.
                script = HERE / checker
                command = [sys.executable, "-B", "-O", str(script), str(path),
                           "--allow-noncanonical", "--json"]
                process = subprocess.run(command, capture_output=True, text=True, cwd=HERE)
                require(process.returncode != 0 and "FAIL:" in process.stderr and "Traceback" not in process.stderr,
                        checker + " failed to reject " + label + ": " + process.stderr)
                outcomes.append({"checker": checker, "test": label + ".O.structural",
                                 "returncode": process.returncode, "expected_success": False,
                                 "stderr": process.stderr.strip()})
        # Whitespace is mathematically harmless but must fail exact-byte mode.
        path = root / "changed_identity.txt"
        path.write_bytes(raw + b"\n")
        for checker in CHECKERS:
            run(checker, ["-O"], path, "changed_identity.O", False)
        # Express the first row with extended terms instead of base terms.
        # This preserves every card but changes both byte digests.
        path = root / "equivalent_encoding.txt"
        path.write_bytes(raw.replace(b"193233", b"740433740533", 1))
        for checker in CHECKERS:
            run(checker, ["-O"], path, "equivalent_encoding.identity.O", False)
            result = run(checker, ["-O"], path, "equivalent_encoding.semantic.O", True,
                         ["--allow-noncanonical"])
            for key in ("reduced_sets_heights_sha256", "full_sets_heights_sha256", "heights_sha256"):
                require(result[key] == reference[key], "equivalent encoding changed " + key)
    receipt = {"status": "PASS", "tests": len(outcomes), "checks": outcomes,
               "complete_reconstructed_arrays_agree": {"cards": 2016, "reduced": True, "full": True},
               "AST_assert_statements": 0,
               "matching_reconstruction": reference,
               "scope": "Finite certificate replay, independent agreement, identity and input rejection; no search or Lean compilation."}
    output = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.evidence:
        (args.evidence / "tests.json").write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
