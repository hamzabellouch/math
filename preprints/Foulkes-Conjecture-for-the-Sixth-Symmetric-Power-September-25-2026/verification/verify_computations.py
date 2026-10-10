#!/usr/bin/env python3
"""Check bundled certificate references, or compile and run both full programs.

Default / --check is read-only and does not execute either C++ program.
--run records fresh compilation and complete execution in a new external
directory (--output PATH, or a newly allocated system temporary directory).
Requires Python 3.9+; only --run requires GNU C++ and Boost headers.
"""

import argparse
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from math import comb
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
PAPER_ROOT = ROOT.parent
SOURCE_SHA256 = {
    "a": "7499d762681cc31e16da8cc042a2e090a1bd14a50fc39b026d9b6f7d7b9e5c38",
    "b": "18da83f7821558764ee9476bb777aa62e821c1ede661484b26de8c8cf789cf6e",
}
STREAM_SHA256 = {
    "a.stdout": "5e721cae45a9ea9b9a3a6e47b75a6e8e5cdf8698efac72aa1cd8abd3457f55af",
    "a.stderr": "bdb44494a5efedabe0f85ab198cc36746f328b2beb53813fe3ee4a84af18c296",
    "b.stdout": "ceebd4910f364036869ae7a619fd67a0c7ffb96db3c37866ea24b7e4decf2f70",
    "b.stderr": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
}


class VerificationError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_json(path):
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def write_json(path, value):
    with path.open("x", encoding="utf-8") as handle:
        json.dump(value, handle, indent=2, sort_keys=True)
        handle.write("\n")


def verify_rows(a_stdout, b_stdout, tables):
    a_lines = a_stdout.decode("utf-8").splitlines()
    require(len(a_lines) == 41, "Appendix A stdout must have exactly 41 rows")
    base, flags = [], []
    for line in a_lines[:20]:
        match = re.fullmatch(r"(\d+) total\(exact\) (\d+) failed (\d+) equality (\d+)", line)
        require(match is not None, f"malformed Appendix A base output: {line!r}")
        b, count, failed, equal = map(int, match.groups())
        require(failed == 0, f"Appendix A reports failures at b={b}")
        base.append([b, count, equal])
    for line in a_lines[20:]:
        match = re.fullmatch(r"(\d+) flags (\d+) max (\d+)", line)
        require(match is not None, f"malformed Appendix A flag output: {line!r}")
        flags.append(list(map(int, match.groups())))
    band = []
    for line in b_stdout.decode("utf-8").splitlines():
        require(re.fullmatch(r"\d+ \d+ \d+", line) is not None,
                f"malformed Appendix B output: {line!r}")
        band.append(list(map(int, line.split())))
    actual = {"base": base, "flags": flags, "band": band}
    for name, rows in actual.items():
        labels = list(range(6, 26)) if name == "base" else list(range(24, 145, 6))
        require([row[0] for row in rows] == labels, f"missing or reordered {name} rows")
    require(actual == tables, "output rows differ from the expected numeric tables")
    return {
        "table_rows": len(base) + len(flags) + len(band),
        "base_exact_comparisons": sum(row[1] for row in base),
        "base_exact_equalities": sum(row[2] for row in base),
        "base_failures": 0,
        "flag_total": sum(row[1] for row in flags),
        "maximum_flag_tail": max(row[2] for row in flags),
        "band_total": sum(row[1] for row in band),
        "band_zero_total": sum(row[2] for row in band),
    }


def check_manuscript_tables(tables, totals):
    def table_with_label(filename, label):
        source = (PAPER_ROOT / "build" / filename).read_text(encoding="utf-8")
        blocks = re.findall(r"\\begin\{table\}.*?\\end\{table\}", source, re.S)
        matches = [block for block in blocks if f"\\label{{{label}}}" in block]
        require(len(matches) == 1, f"expected one manuscript table {label}")
        return matches[0]

    base_text = table_with_label("sections/certificates.tex", "tab:base")
    row_end = r"[ \t]*(?:\\\\[ \t]*(?:\\hline)?)?[ \t]*$"
    rows = re.findall(r"^[ \t]*(\d+)&(\d+)&(\d+)&(\d+)&(\d+)&(\d+)" + row_end, base_text, re.M)
    base = sorted([list(map(int, row[offset:offset + 3]))
                   for row in rows for offset in (0, 3)])
    require(base == tables["base"], "manuscript base table differs from expected rows")
    band_text = table_with_label("sections/verification.tex", "tab:band")
    rows = re.findall(r"^[ \t]*(\d+)--(\d+)&(\d+)&(\d+)&(\d+)&(\d+)" + row_end, band_text, re.M)
    expected = [[max(26, f[0]), f[0] + 5, f[1], f[2], b[1], b[2]]
                for f, b in zip(tables["flags"], tables["band"])]
    require([list(map(int, row)) for row in rows] == expected,
            "manuscript band table differs from expected rows or degree ranges")
    total = re.findall(r"^total&(\d+)&(\d+)&(\d+)&(\d+)" + row_end, band_text, re.M)
    expected_total = [totals[k] for k in ("flag_total", "maximum_flag_tail", "band_total", "band_zero_total")]
    require(len(total) == 1 and list(map(int, total[0])) == expected_total,
            "manuscript band totals differ")


def check_bounds_and_counts(manifest):
    # Restricted-part partition counts are conjugate to the padded levels used
    # by the C++ rank arrays. These small integer checks do not run certificates.
    partitions = [[1] + [0] * 894]
    for parts in range(1, 7):
        row = partitions[-1].copy()
        for n in range(parts, len(row)):
            row[n] += row[n - parts]
        partitions.append(row)
    tail = sum(partitions[3][270 - a - b - c - 3 * a]
               for a in range(19) for b in range(a + 1) for c in range(b + 1)
               if a + b + c <= 18)
    counts = {"six_variable_level": partitions[6][150],
              "four_variable_level": partitions[4][330],
              "three_variable_level": partitions[3][894],
              "tail_level": tail, "grid": sum(partitions[5][:150])}
    require(counts == manifest["index_counts"], "index count summary differs")
    require(comb(1254, 5) < 2**63, "prefix count bound fails")
    require(max(comb(155, 5), comb(333, 3), comb(896, 2), comb(154, 5),
                comb(21, 3) * comb(272, 2)) < 2**31, "index bound fails")
    require(151**10 * (6 * 151**4 + 6) < 2**127, "source accumulation bound fails")
    require(720 * 920**10 < 720 * 2**100 < 2**127, "cycle upper bound fails")
    require(610 * 150 * 2**100 < 2**127, "binomial-search bound fails")
    require(comb(167, 18) < 2**127, "capped binomial bound fails")
    multiplicities = [(7 - h) * comb(h + 3, 3) for h in range(1, 7)]
    require(multiplicities == [24, 50, 80, 105, 112, 84], "band factor counts differ")
    norm = Fraction(4**27)
    for h, count in enumerate(multiplicities, 1):
        norm *= Fraction(4**h, 4**h - 1)**count
    require(norm < 2**79, "band norm bound fails")
    source_norm, quotient_norm = comb(51, 24), 64 * comb(21, 6)
    require(source_norm < 2**51 and quotient_norm == 3472896 < 2**22,
            "source or quotient norm bound fails")
    require(64 * comb(27, 6) == 18944640 < 2**31 and comb(32, 5) == 201376 < 2**31,
            "small integer array bounds fail")
    band_bound = 512 * 24 * (27 * 720 * 64 * 2**79 + 5040 * quotient_norm * source_norm)
    require(band_bound < 2**115 < 2**127, "predivision coefficient bound fails")
    require(manifest["ranges"] == {"base": [6, 25], "flags_and_band": [26, 149],
            "required_with_quadratic_companion": [6, 29], "supplemental": [30, 149],
            "band_tail_at_most": 27}, "certificate range summary differs")
    return {"index_counts": counts, "band_predivision_bound": band_bound,
            "signed_128_limit": 2**127, "arithmetic_inequalities": "passed"}


def check():
    manifest = read_json(ROOT / "support/expected-results.json")
    require(manifest["schema_version"] == 2, "unsupported expectation schema")
    expected_hashes = {f"programs/appendix-{key}.cpp": value for key, value in SOURCE_SHA256.items()}
    expected_hashes.update({f"support/expected/appendix-{key}": value for key, value in STREAM_SHA256.items()})
    require(manifest["file_sha256"] == expected_hashes, "manifest source or stream identities differ")
    for relative, expected in expected_hashes.items():
        require(digest((ROOT / relative).read_bytes()) == expected, f"SHA-256 mismatch: {relative}")
    totals = verify_rows((ROOT / "support/expected/appendix-a.stdout").read_bytes(),
                         (ROOT / "support/expected/appendix-b.stdout").read_bytes(), manifest["tables"])
    require(totals == manifest["totals"] and totals["table_rows"] == 62,
            "computed result totals differ from expected 62-row summary")
    require(totals["maximum_flag_tail"] <= 27, "flag exceeds the checked tail band")
    require(manifest["mode_counts"] == {"minimal_common_occurrences": 15,
            "common_occurrence_degree": 42, "todos": 87354, "down": 114314,
            "maximum_occurrence_vector": 15}, "mode count summary differs")
    check_manuscript_tables(manifest["tables"], totals)
    bounds = check_bounds_and_counts(manifest)
    return manifest, {"status": "passed", "mode": "check", "certificate_programs_executed": False,
                      "totals": totals, "bounds": bounds}


def command_run(command, directory, label, environment):
    """Capture one child without a shell, retaining failures and interruptions."""
    import resource

    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.monotonic()
    record = {"command": command, "cwd": str(directory), "environment": environment,
              "started_utc": datetime.now(timezone.utc).isoformat()}
    try:
        with (directory / f"{label}.stdout").open("xb") as out, \
                (directory / f"{label}.stderr").open("xb") as err:
            process = subprocess.Popen(command, cwd=directory, env=environment, stdout=out, stderr=err)
            try:
                record["exit_code"] = process.wait()
            except BaseException:
                process.kill()
                record["exit_code"] = process.wait()
                record["interrupted"] = True
                raise
    except OSError as exc:
        record["exit_code"] = None
        record["launch_error"] = str(exc)
    finally:
        after = resource.getrusage(resource.RUSAGE_CHILDREN)
        record.update({"elapsed_seconds": time.monotonic() - start,
                       "ended_utc": datetime.now(timezone.utc).isoformat(),
                       "user_seconds": after.ru_utime - before.ru_utime,
                       "system_seconds": after.ru_stime - before.ru_stime,
                       "max_rss_kib": after.ru_maxrss,
                       "max_rss_note": "Linux cumulative RUSAGE_CHILDREN high-water mark; includes earlier children"})
        for stream in ("stdout", "stderr"):
            path = directory / f"{label}.{stream}"
            if path.exists():
                record[f"{stream}_sha256"] = digest(path.read_bytes())
        write_json(directory / f"{label}.json", record)
    require(record.get("exit_code") == 0, f"{label} failed; see {directory / (label + '.json')}")
    return record


def new_directory(output):
    if output is None:
        temporary_root = Path(tempfile.gettempdir()).resolve()
        require(temporary_root != PAPER_ROOT and PAPER_ROOT not in temporary_root.parents,
                "temporary directory must be outside the paper directory")
        directory = Path(tempfile.mkdtemp(prefix="foulkes-sixth-computation-", dir=temporary_root))
    else:
        requested = Path(output).expanduser()
        require(not requested.exists() and not requested.is_symlink(), "output directory must not already exist")
        directory = requested.resolve()
        require(directory != PAPER_ROOT and PAPER_ROOT not in directory.parents,
                "output directory must be outside the paper directory")
        directory.mkdir(mode=0o700)
    return directory.resolve()


def run(manifest, check_result, args):
    compiler = shutil.which(args.compiler)
    require(compiler is not None, f"compiler not found: {args.compiler}")
    compiler = str(Path(compiler).resolve())
    directory = new_directory(args.output)
    environment = {"PATH": os.defpath, "LANG": "C", "LC_ALL": "C", "TMPDIR": str(directory),
                   "OMP_NUM_THREADS": str(args.threads), "OMP_DYNAMIC": "FALSE"}
    result = {"status": "failed", "mode": "run", "directory": str(directory),
              "source_sha256": SOURCE_SHA256, "assertions_enabled": True,
              "binary_sha256": {},
              "openmp_appendix_a": not args.serial,
              "verifier_sha256": digest(Path(__file__).read_bytes()),
              "manifest_sha256": digest((ROOT / "support/expected-results.json").read_bytes()),
              "checks_before": check_result}
    print(f"Run artifacts: {directory}", flush=True)
    try:
        command_run([compiler, "--version"], directory, "compiler-version", environment)
        for key in ("a", "b"):
            source = (ROOT / f"programs/appendix-{key}.cpp").read_bytes()
            require(digest(source) == SOURCE_SHA256[key], "program changed after initial check")
            local_source = directory / f"appendix-{key}.cpp"
            with local_source.open("xb") as handle:
                handle.write(source)
            binary = directory / f"appendix-{key}"
            command = [compiler, "-std=c++17", "-O3", "-UNDEBUG"]
            if key == "a" and not args.serial:
                command.append("-fopenmp")
            command.extend([str(local_source), "-o", str(binary)])
            print(f"Building Appendix {key.upper()} (assertions enabled)", flush=True)
            command_run(command, directory, f"appendix-{key}-build", environment)
            result["binary_sha256"][key] = digest(binary.read_bytes())
        for key in ("a", "b"):
            binary = directory / f"appendix-{key}"
            run_environment = dict(environment)
            if key == "b" or args.serial:
                run_environment["OMP_NUM_THREADS"] = "1"
            print(f"Running Appendix {key.upper()} over its complete range", flush=True)
            execution = command_run([str(binary)], directory, f"appendix-{key}-run", run_environment)
            execution["binary_sha256"] = digest(binary.read_bytes())
            execution["source_sha256"] = digest((directory / f"appendix-{key}.cpp").read_bytes())
            result[f"appendix_{key}"] = execution
            for stream in ("stdout", "stderr"):
                actual = (directory / f"appendix-{key}-run.{stream}").read_bytes()
                expected = (ROOT / f"support/expected/appendix-{key}.{stream}").read_bytes()
                require(actual == expected, f"Appendix {key.upper()} {stream} differs byte-for-byte; see {directory}")
        result["totals"] = verify_rows((directory / "appendix-a-run.stdout").read_bytes(),
                                      (directory / "appendix-b-run.stdout").read_bytes(), manifest["tables"])
        _, result["checks_after"] = check()
        require(digest((ROOT / "support/expected-results.json").read_bytes()) == result["manifest_sha256"],
                "expectation manifest changed during execution")
        require(digest(Path(__file__).read_bytes()) == result["verifier_sha256"],
                "verification helper changed during execution")
        result["status"] = "passed"
    except BaseException as exc:
        result["error"] = str(exc) or type(exc).__name__
        raise
    finally:
        write_json(directory / "result.json", result)
    print("PASS: both freshly compiled programs exited zero and matched stdout/stderr exactly.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="read-only reference checks (default)")
    mode.add_argument("--run", action="store_true", help="compile and run both complete exact programs")
    parser.add_argument("--output", help="new external run directory; parent must exist")
    parser.add_argument("--compiler", default="g++", help="C++ compiler executable for --run")
    parser.add_argument("--serial", action="store_true", help="compile Appendix A without optional OpenMP")
    parser.add_argument("--threads", type=int, default=2, help="Appendix A OpenMP threads (default: 2)")
    args = parser.parse_args()
    if args.threads < 1:
        parser.error("--threads must be positive")
    if not args.run and (args.output or args.serial or args.threads != 2 or args.compiler != "g++"):
        parser.error("--output, --compiler, --serial, and --threads require --run")
    try:
        manifest, result = check()
        print(json.dumps(result, indent=2, sort_keys=True))
        print("PASS: bundled source/stream identities, 62 expected rows, manuscript tables, and numeric bounds.")
        print("CHECK ONLY: neither certificate program has been executed by these checks.")
        if args.run:
            run(manifest, result, args)
        return 0
    except (VerificationError, OSError, ValueError, KeyError, TypeError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("FAIL: interrupted", file=sys.stderr)
        return 130


if __name__ == "__main__":
    sys.exit(main())
