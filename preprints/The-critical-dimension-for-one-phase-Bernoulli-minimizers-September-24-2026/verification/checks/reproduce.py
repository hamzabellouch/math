#!/usr/bin/env python3
"""Reproduce the archived finite arithmetic checks without changing the archive.

This checks provenance, literal table rows, and deterministic arithmetic output.
It does not check equivalence between manuscript formulas and program formulas.
"""

import argparse
import hashlib
from itertools import islice
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tempfile
import time


MANIFEST_SHA256 = "0deab5ebf5c970b844379cb6bdb406d1ce73815fb550a8e3e3ae08a083b990de"
SOURCE_SHA256 = "3b1e67b40af1740a1faab1ee8bbe85aa7c90dcb289fb5df2c8880de6956a8ffc"
INPUT_NAME = "certificate-inputs.txt"
ARCHIVE_FILE_COUNT = 12
INDEPENDENT_PROVENANCE_SHA256 = "78051e27f8705739b6d9b0b57e32dfb47ab64b26f21e3ae8b015663de44d5112"
INDEPENDENT_FILES = {
    "engine.py", "bounds.py", "compare_oracle.py", "README.md",
    "first-freeze.json", "output/coefficients.json",
    "output/results.json", "output/oracle-comparison.json",
}
INDEPENDENT_SCRIPTS = ("engine.py", "bounds.py", "compare_oracle.py")
CHECKS = (
    ("exact-replay.py", "exact-results.json", False),
    ("boundary-independent.py", "boundary-independent-results.json", False),
    ("algebra-independent.py", "algebra-independent-result.json", True),
    ("algebra-debate-graphs.py", "algebra-debate-graphs.json", True),
)
RESULT_SOURCE_DIGEST_FIELDS = {
    "boundary-independent.py": "implementation_sha256",
    "algebra-independent.py": "source_sha256",
}
REDACTED_ORACLE_PATH = "[redacted historical absolute path]"
VERBATIM_BEGIN = b"\\begin{Verbatim}[fontsize=\\footnotesize]"
VERBATIM_END = b"\\end{Verbatim}"
TABLE_DELIMITERS = {
    "I": (b"\\begin{multicols}{2}", b"\\end{multicols}"),
    "II": (b"\\begingroup\\clubpenalty=10000\\widowpenalty=10000", b"\\endgroup"),
}


class CheckFailure(RuntimeError):
    """A failed integrity, table, dependency, or reproduction check."""


def digest(data):
    return hashlib.sha256(data).hexdigest()


def verify_file(path, record):
    """Validate both byte length and SHA-256; this remains active under -O."""
    if path.is_symlink() or not path.is_file():
        raise CheckFailure(f"Missing regular file: {path}")
    raw = path.read_bytes()
    if len(raw) != record["bytes"]:
        raise CheckFailure(f"Byte length mismatch: {path}")
    if digest(raw) != record["sha256"]:
        raise CheckFailure(f"SHA-256 mismatch: {path}")


def verify_archive(original):
    """Pin the manifest first, then validate every listed file and archive path."""
    if original.is_symlink() or not original.is_dir():
        raise CheckFailure(f"Missing regular archive directory: {original}")
    manifest_path = original / "final-integrity.json"
    if manifest_path.is_symlink() or not manifest_path.is_file():
        raise CheckFailure(f"Missing regular manifest: {manifest_path}")
    raw = manifest_path.read_bytes()
    if digest(raw) != MANIFEST_SHA256:
        raise CheckFailure("Frozen manifest SHA-256 mismatch")
    manifest = json.loads(raw)
    if manifest.get("schema") != "bernoulli-critical-dimension-portable-required-inputs-v1":
        raise CheckFailure("Unexpected frozen manifest schema")
    if manifest.get("source_sha256") != SOURCE_SHA256:
        raise CheckFailure("Unexpected source digest in frozen manifest")
    records = manifest.get("files")
    if not isinstance(records, list) or len(records) != ARCHIVE_FILE_COUNT:
        raise CheckFailure("Frozen manifest must describe exactly 12 required computation files")
    by_path = {}
    for record in records:
        name = record.get("path")
        if not isinstance(name, str):
            raise CheckFailure("Invalid manifest file path")
        path = PurePosixPath(name)
        if path.is_absolute() or ".." in path.parts or str(path) != name:
            raise CheckFailure(f"Unsafe manifest file path: {name}")
        if name in by_path or name == "final-integrity.json":
            raise CheckFailure(f"Duplicate manifest file path: {name}")
        if type(record.get("bytes")) is not int or record["bytes"] < 0:
            raise CheckFailure(f"Invalid byte length: {name}")
        if not re.fullmatch(r"[0-9a-f]{64}", record.get("sha256", "")):
            raise CheckFailure(f"Invalid SHA-256: {name}")
        by_path[name] = record

    # Reject extra files and symlinks before copying or executing archived code.
    actual = set()
    for path in original.rglob("*"):
        if path.is_symlink():
            raise CheckFailure(f"Archive contains a symlink: {path}")
        if path.is_file():
            actual.add(path.relative_to(original).as_posix())
        elif not path.is_dir():
            raise CheckFailure(f"Archive contains a nonregular entry: {path}")
    expected = set(by_path) | {"final-integrity.json"}
    if actual != expected:
        raise CheckFailure(
            f"Archive file set differs: missing={sorted(expected - actual)}, "
            f"unexpected={sorted(actual - expected)}"
        )
    for name, record in by_path.items():
        verify_file(original / name, record)
    return by_path


def verify_extraction(original):
    """Compare each entire fenced table/source body with its archived extract."""
    source = (original / INPUT_NAME).read_bytes()
    bodies = re.findall(rb"^~~~\n(.*?)^~~~(?:\n|$)", source, re.MULTILINE | re.DOTALL)
    names = ("exact-table-I.txt", "exact-table-II.txt", "exact-source.py")
    if len(bodies) != len(names):
        raise CheckFailure("Expected exactly three fenced bodies in the certificate input")
    for name, body in zip(names, bodies):
        if body != (original / "checks" / name).read_bytes():
            raise CheckFailure(f"Literal source extraction mismatch: {name}")
    independent_input_digest(original / INPUT_NAME)
    return bodies[:2]


def independent_input_digest(path):
    """Authenticate the table-only prefix read by the unchanged independent engine."""
    with path.open(encoding="utf-8") as stream:
        prefix = "".join(islice(stream, 1124))
    if len(re.findall(r"(?m)^~~~(?:\n|$)", prefix)) != 4:
        raise CheckFailure("Independent input prefix must contain exactly two fenced tables")
    return digest(prefix.encode("utf-8"))


def verify_independent(independent):
    """Pin the independent record and require matching distributed source copies."""
    if independent.is_symlink() or not independent.is_dir():
        raise CheckFailure(f"Missing regular independent directory: {independent}")
    provenance_path = independent / "provenance.json"
    if provenance_path.is_symlink() or not provenance_path.is_file():
        raise CheckFailure("Missing regular independent provenance record")
    if digest(provenance_path.read_bytes()) != INDEPENDENT_PROVENANCE_SHA256:
        raise CheckFailure("Independent provenance SHA-256 mismatch")
    records = json.loads(provenance_path.read_bytes())["artifacts"]
    if set(records) != INDEPENDENT_FILES:
        raise CheckFailure("Unexpected independent provenance file set")
    for name, record in records.items():
        path = independent / name
        if path.parent.is_symlink():
            raise CheckFailure(f"Independent input has a symlink parent: {path}")
        verify_file(path, record)
    freeze = json.loads((independent / "first-freeze.json").read_bytes())["files"]
    for name in ("engine.py", "bounds.py"):
        verify_file(independent / (name + ".first-frozen"), records[name])
        if freeze.get(name) != records[name]["sha256"]:
            raise CheckFailure(f"Independent first-freeze mismatch: {name}")
        if (independent / name).read_bytes() != (independent / (name + ".first-frozen")).read_bytes():
            raise CheckFailure(f"Independent source differs from first-frozen copy: {name}")
    return records


def typeset_table_body(tex, label):
    """Strip only the explicitly allowed Verbatim wrapper lines, in order."""
    lines = tex.split(b"\n")
    begin, end = TABLE_DELIMITERS[label]
    if lines.count(begin) != 1 or lines.count(end) != 1:
        raise CheckFailure(f"Table {label}: expected exactly one delimiter pair")
    first, last = lines.index(begin), lines.index(end)
    if first >= last:
        raise CheckFailure(f"Table {label}: reversed delimiters")
    body = []
    opened = False
    blocks = 0
    for line in lines[first + 1:last]:
        if line == VERBATIM_BEGIN:
            if opened:
                raise CheckFailure(f"Table {label}: nested Verbatim environment")
            opened = True
            blocks += 1
        elif line == VERBATIM_END:
            if not opened:
                raise CheckFailure(f"Table {label}: unmatched Verbatim end")
            opened = False
        elif opened:
            body.append(line)
        else:
            raise CheckFailure(f"Table {label}: text outside Verbatim inside delimiters")
    if opened or blocks == 0:
        raise CheckFailure(f"Table {label}: incomplete Verbatim environment")
    return b"\n".join(body) + b"\n"


def verify_typeset_tables(tables_path, bodies):
    tex = tables_path.read_bytes()
    for label, expected in zip(("I", "II"), bodies):
        if typeset_table_body(tex, label) != expected:
            raise CheckFailure(f"Typeset Table {label} differs from literal source rows")


def child_environment():
    env = os.environ.copy()
    env.pop("PYTHONOPTIMIZE", None)
    return env


def child_command(*args):
    # -I also ignores inherited PYTHON* settings and the user's site directory.
    # No -O/-OO flag from the wrapper is propagated to this fresh interpreter.
    return [sys.executable, "-I", "-B", "-u", "-X", "utf8", *map(str, args)]


def independent_command(script, *args):
    """Allow sibling imports only from the directory of staged verified scripts."""
    bootstrap = (
        "import runpy, sys\n"
        "from pathlib import Path\n"
        "if sys.flags.optimize != 0: raise RuntimeError('Assertions must be enabled')\n"
        "script = Path(sys.argv[1]).resolve()\n"
        "sys.path.insert(0, str(script.parent))\n"
        "sys.argv = sys.argv[1:]\n"
        "runpy.run_path(str(script), run_name='__main__')\n"
    )
    return child_command("-c", bootstrap, script, *args)


def check_dependencies():
    code = (
        "import sys\n"
        "if sys.flags.optimize != 0: raise RuntimeError('Assertions must be enabled')\n"
        "if sys.byteorder != 'little': raise RuntimeError('Frozen NumPy hashes require little-endian')\n"
        "import resource\n"
        "import numpy\n"
        "print('Python ' + sys.version.split()[0] + '; NumPy ' + numpy.__version__)\n"
    )
    result = subprocess.run(
        child_command("-c", code), env=child_environment(),
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if result.returncode:
        raise CheckFailure(
            "Replay needs a little-endian POSIX Python with NumPy installed in "
            "its environment (not only the user site).\n"
            + result.stderr.decode("utf-8", errors="replace")
        )
    print("PASS dependencies: " + result.stdout.decode("utf-8").strip(), flush=True)


def run_program(command, directory, label):
    """Run an isolated child, preserving diagnostics and bounded progress waits."""
    started = time.monotonic()
    print(f"RUN {label}", flush=True)
    with subprocess.Popen(
        command, cwd=directory,
        env=child_environment(), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    ) as process:
        while True:
            try:
                stdout, stderr = process.communicate(timeout=30)
                break
            except subprocess.TimeoutExpired:
                elapsed = int(time.monotonic() - started)
                print(f"RUN {label}: still computing ({elapsed} seconds)", flush=True)
        if process.returncode:
            details = (stdout + stderr).decode("utf-8", errors="replace")
            raise CheckFailure(f"{label} exited with code {process.returncode}\n{details}")
    return stdout


def run_check(stage, script, output, stdout_is_result, records):
    """Run one copied script and require a newly produced deterministic artifact."""
    target = stage / "checks" / output
    # A script that exits successfully without producing output must not pass
    # because a frozen expected output was present in the copied archive.
    expected = None
    if target.exists():
        verify_file(target, records["checks/" + output])
        expected = target.read_bytes()
    if target.exists():
        target.unlink()
    stdout = run_program(child_command(stage / "checks" / script), stage, script)
    if stdout_is_result:
        target.write_bytes(stdout)
    source_field = RESULT_SOURCE_DIGEST_FIELDS.get(script)
    if source_field is None:
        verify_file(target, records["checks/" + output])
        if expected is not None and target.read_bytes() != expected:
            raise CheckFailure(f"Byte comparison mismatch: {output}")
        print(f"PASS {output}: {records['checks/' + output]['sha256']}", flush=True)
    else:
        if target.is_symlink() or not target.is_file():
            raise CheckFailure(f"Missing regular file: {target}")
        if expected is None:
            raise CheckFailure(f"Missing historical result: {output}")
        compare_historical_result(
            target.read_bytes(), expected,
            {
                "input_sha256": SOURCE_SHA256,
                source_field: records["checks/" + script]["sha256"],
            },
        )
        print(f"PASS {output}: historical payload and current input/source digests", flush=True)


def compare_historical_result(actual_raw, expected_raw, current_digests):
    """Validate current digests, then require all other bytes to match the historical result."""
    actual = json.loads(actual_raw)
    expected = json.loads(expected_raw)
    if not isinstance(actual, dict) or not isinstance(expected, dict):
        raise CheckFailure("Digest-bearing results must be JSON objects")
    normalized = actual_raw
    for field, current in current_digests.items():
        if not isinstance(current, str) or not re.fullmatch(r"[0-9a-f]{64}", current):
            raise CheckFailure(f"Invalid current digest for {field}")
        if actual.get(field) != current:
            raise CheckFailure(f"Current {field} does not match the authenticated input or source")
        historical = expected.get(field)
        if not isinstance(historical, str) or not re.fullmatch(r"[0-9a-f]{64}", historical):
            raise CheckFailure(f"Historical result has no valid {field}")
        key = json.dumps(field).encode("ascii") + b": "
        current_token = key + json.dumps(current).encode("ascii")
        historical_token = key + json.dumps(historical).encode("ascii")
        if normalized.count(current_token) != 1 or expected_raw.count(historical_token) != 1:
            raise CheckFailure(f"Result must contain one canonical {field} field")
        normalized = normalized.replace(current_token, historical_token, 1)
    if normalized != expected_raw:
        raise CheckFailure("Result bytes differ from the historical result outside validated digests")
    return digest(normalized)


def verify_comparison(generated, preserved, oracle):
    """Compare every report field except the separately validated absolute path."""
    actual = json.loads(generated.read_bytes())
    expected = json.loads(preserved.read_bytes())
    if not isinstance(actual, dict) or not isinstance(expected, dict):
        raise CheckFailure("Independent comparison must be a JSON object")
    if actual.get("passed") is not True:
        raise CheckFailure("Independent oracle comparison did not pass")
    if actual.get("oracle_path") != str(oracle.resolve()):
        raise CheckFailure("Independent comparison recorded an unexpected oracle path")
    if expected.get("oracle_path") != REDACTED_ORACLE_PATH:
        raise CheckFailure("Preserved comparison must explicitly mark its historical oracle path redacted")
    actual.pop("oracle_path")
    expected.pop("oracle_path")
    canonical = lambda value: json.dumps(value, sort_keys=True, separators=(",", ":")).encode("ascii")
    payload = canonical(actual)
    if payload != canonical(expected):
        raise CheckFailure("Independent oracle comparison differs from the preserved report")
    return digest(payload)


def run_independent(reference, stage, original, records):
    """Rebuild independent coefficients before exposing the comparison oracle."""
    stage.mkdir()
    for name in INDEPENDENT_SCRIPTS:
        shutil.copyfile(reference / name, stage / name)
        verify_file(stage / name, records[name])
    # Deliberately do not copy old outputs, imports, or bytecode into this stage.
    output = stage / "output"
    run_program(independent_command(stage / "bounds.py"), stage, "independent bounds self-checks")
    run_program(
        independent_command(stage / "engine.py", "--input", original / INPUT_NAME, "--out", output),
        stage, "independent full interior expansion",
    )
    name = "coefficients.json"
    verify_file(output / name, records["output/" + name])
    if (output / name).read_bytes() != (reference / "output" / name).read_bytes():
        raise CheckFailure(f"Independent byte comparison mismatch: {name}")
    print(f"PASS independent {name}: {records['output/' + name]['sha256']}", flush=True)
    name = "results.json"
    if (output / name).is_symlink() or not (output / name).is_file():
        raise CheckFailure(f"Missing regular file: {output / name}")
    compare_historical_result(
        (output / name).read_bytes(), (reference / "output" / name).read_bytes(),
        {"input_prefix_sha256": independent_input_digest(original / INPUT_NAME)},
    )
    print(f"PASS independent {name}: historical payload and current input digest", flush=True)
    oracle = original / "checks" / "exact-results.json"
    run_program(
        independent_command(stage / "compare_oracle.py", "--oracle", oracle, "--output", output),
        stage, "independent coefficient comparison",
    )
    comparison_sha = verify_comparison(
        output / "oracle-comparison.json", reference / "output" / "oracle-comparison.json", oracle,
    )
    print(f"PASS independent comparison, excluding validated path: {comparison_sha}", flush=True)


def reproduce(writeup, verify_inputs_only=False):
    original = writeup / "checks" / "original"
    independent = writeup / "independent-certificate"
    records = verify_archive(original)
    print("PASS pinned manifest and all 12 required computation files", flush=True)
    bodies = verify_extraction(original)
    print("PASS exact extraction of both tables and the submitted Python source", flush=True)
    verify_typeset_tables(writeup.parent / "build" / "appendices" / "tables.tex", bodies)
    print("PASS literal rows in both typeset tables", flush=True)
    independent_records = verify_independent(independent)
    print("PASS independent provenance and matching distributed source copies", flush=True)
    if verify_inputs_only:
        print("PASS bounded input-only verification; arithmetic engines were not executed", flush=True)
        return
    check_dependencies()
    with tempfile.TemporaryDirectory(prefix="bernoulli-reproduce-") as temporary:
        stage = Path(temporary) / "original"
        shutil.copytree(original, stage)
        verify_archive(stage)
        for script, output, stdout_is_result in CHECKS:
            run_check(stage, script, output, stdout_is_result, records)
        run_independent(independent, Path(temporary) / "independent", stage, independent_records)
    # Detect an accidental original-file change during reproduction as well.
    verify_archive(original)
    verify_independent(independent)
    print("PASS both full interior engines and all supporting checks; frozen evidence unchanged", flush=True)
    print(
        "Scope: provenance, literal table rows, two complete interior expansions, "
        "their exact coefficient comparison, and the boundary/projection/graph checks. "
        "Manuscript formula equivalence and the analytic proof require mathematical review.",
        flush=True,
    )


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-inputs-only", action="store_true", help="Verify clean input hashes, exact table extraction and independent frozen inputs without running arithmetic engines")
    args = parser.parse_args(argv)
    try:
        reproduce(Path(__file__).resolve().parents[1], verify_inputs_only=args.verify_inputs_only)
    except (CheckFailure, OSError, ValueError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr, flush=True)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
