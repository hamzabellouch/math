#!/usr/bin/env python3
"""Reproduce the finite numerical certificate. No package installation or networking.

This driver does not prove the mathematical reduction to matrix multiplication.
All arithmetic checker assertions remain enabled. See README.md.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import time

PACKAGE = Path(__file__).resolve().parent
CHARTS = {
    "qP420_gmp": (420, 224, "7dc037ea127cece2216f3219eeeca4cdab0288319a10111a78d272586b776f0b"),
    "qP780_gmp": (780, 500, "f23c0480f1109509545fdd17bb4de81602f50952411554b337105defbe7a070c"),
}
STAGED_PATHS = {
    "checkers/gen.py": "local-check/gen.py",
    "checkers/ib.cpp": "local-check/ib.cpp",
    "checkers/menu.hpp": "local-check/menu.hpp",
    "checkers/run_interior.py": "local-check/run_interior.py",
    "checkers/verify_summary.py": "local-check/verify_summary.py",
    "checkers/pgen.py": "checkers/pgen.py",
    "checkers/rooLS.cpp": "checkers/rooLS.cpp",
    "checkers/rooLS.py": "checkers/rooLS.py",
    "checkers/check_tensor_primitives.cpp": "checkers/check_tensor_primitives.cpp",
    "checkers/chart_gmp.cpp": "audit/chart-check/chart_gmp.cpp",
    "checkers/certify_chart.py": "audit/chart-check/certify_chart.py",
    "checkers/verify_recorded_bounds.py": "audit/chart-check/verify_recorded_bounds.py",
    "checkers/pgeo.py": "audit/chart-check/geometry/pgeo.py",
    "inputs/newc22": "inputs/newc22",
}
REQUIRED = list(STAGED_PATHS)



def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def manifest_hashes():
    path = PACKAGE / "package-manifest.json"
    if not path.is_file():
        raise RuntimeError("Missing package-manifest.json")
    content = json.loads(path.read_text())
    entries = content.get("files", content)
    if isinstance(entries, list):
        return {item["path"]: item["sha256"] for item in entries}
    return {name: (value["sha256"] if isinstance(value, dict) else value)
            for name, value in entries.items()}


def checked_package_file(relative, hashes):
    path = PACKAGE / relative
    if not path.is_file():
        raise RuntimeError("Missing packaged file: " + relative)
    expected = hashes.get(relative)
    if not expected or digest(path) != expected:
        raise RuntimeError("Missing or mismatching manifest SHA-256: " + relative)
    return path


def pkg_config(option):
    if not shutil.which("pkg-config"):
        return None
    result = subprocess.run(["pkg-config", option, "gmpxx"], text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    return shlex.split(result.stdout) if result.returncode == 0 else None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", type=Path, default=PACKAGE / "reproduction-work",
                        help="New or empty output directory (default: beside this script)")
    parser.add_argument("--reuse-charts", action="store_true",
                        help="Verify and copy the packaged charts instead of regenerating them")
    parser.add_argument("--cxx", default=os.environ.get("CXX"),
                        help="C++ compiler command; falls back to CXX, clang++, then g++")
    parser.add_argument("--gmp-cflags", default=os.environ.get("GMP_CFLAGS"),
                        help="GMP include flags; default: pkg-config --cflags gmpxx")
    parser.add_argument("--gmp-libs", default=os.environ.get("GMP_LIBS"),
                        help="GMP linker flags; default: pkg-config --libs gmpxx, or -lgmpxx -lgmp")
    args = parser.parse_args()
    if not __debug__:
        parser.error("Do not use python -O: the certificate requires assertions")
    if os.name != "posix":
        parser.error("The interior runner requires POSIX fork (Linux or macOS)")
    cxx = shlex.split(args.cxx) if args.cxx else []
    if not cxx:
        candidate = shutil.which("clang++") or shutil.which("g++")
        if candidate:
            cxx = [candidate]
    if not cxx or not shutil.which(cxx[0]):
        parser.error("A C++17 compiler with __int128 and UndefinedBehaviorSanitizer is required")
    if any(flag.startswith("-DNDEBUG") for flag in cxx):
        parser.error("CXX must not disable assertions with -DNDEBUG")
    hashes = manifest_hashes()
    for relative in REQUIRED:
        checked_package_file(relative, hashes)
    if args.reuse_charts:
        for name in CHARTS:
            checked_package_file("inputs/" + name, hashes)
    work = args.work_dir.expanduser().resolve()
    if work.exists() and (not work.is_dir() or any(work.iterdir())):
        parser.error("--work-dir must be new or empty; existing results are never overwritten")
    work.mkdir(parents=True, exist_ok=True)
    local = work / "local-check"
    chart_dir = work / "audit/chart-check"
    changes = []
    commands = []
    environment = os.environ.copy()
    environment.pop("PYTHONOPTIMIZE", None)
    environment["PYTHONUNBUFFERED"] = "1"

    def record():
        (work / "driver-provenance.json").write_text(json.dumps({
            "package": str(PACKAGE), "work_dir": str(work),
            "python": sys.executable, "cxx": cxx,
            "reuse_charts": args.reuse_charts,
            "source_adaptations": changes, "commands": commands,
        }, indent=2) + "\n")

    def stage(relative, replacements=()):
        source = checked_package_file(relative, hashes)
        destination = work / STAGED_PATHS[relative]
        destination.parent.mkdir(parents=True, exist_ok=True)
        data = source.read_bytes()
        edits = []
        if replacements:
            text = data.decode()
            for before, after, reason in replacements:
                count = text.count(before)
                if count != 1:
                    raise RuntimeError(f"Expected exactly one substitution in {relative}: {before!r}; found {count}")
                text = text.replace(before, after)
                edits.append({"before": before, "after": after, "reason": reason})
            data = text.encode()
        destination.write_bytes(data)
        changes.append({"file": relative, "work_file": STAGED_PATHS[relative],
                        "package_sha256": digest(source),
                        "work_sha256": digest(destination), "substitutions": edits})
        record()

    def run(label, command, cwd=work, log=None):
        path = log or work / "logs" / (label + ".log")
        path.parent.mkdir(parents=True, exist_ok=True)
        entry = {"stage": label, "argv": list(map(str, command)), "cwd": str(cwd),
                 "log": str(path.relative_to(work))}
        commands.append(entry)
        record()
        print(f"[{label}] {shlex.join(entry['argv'])}\n  log: {path}", flush=True)
        start = time.monotonic()
        with path.open("wb") as output:
            result = subprocess.run(entry["argv"], cwd=cwd, env=environment,
                                    stdout=output, stderr=subprocess.STDOUT)
        entry.update(exit_code=result.returncode, seconds=time.monotonic() - start)
        record()
        if result.returncode:
            raise RuntimeError(f"Stage {label} exited {result.returncode}; see {path}")
        print(f"[{label}] PASS ({entry['seconds']:.1f}s)", flush=True)

    original_qp = "'qP'"
    for relative in REQUIRED:
        replacements = []
        if relative in ("checkers/certify_chart.py", "checkers/pgeo.py"):
            replacements.append((original_qp, repr(str(local / "qP")), "data path only"))
        if relative == "checkers/run_interior.py":
            replacements.append(('src = ROOT / "source/dynamic-edit-recovery/full-cat"',
                                 'src = ROOT / "checkers"', "checker source path only"))
            replacements.append(('["clang++", "-std=c++17"',
                                 repr(cxx)[:-1] + ', "-std=c++17"',
                                 "compiler command selection only; retain sanitizer and optimization flags"))
        stage(relative, replacements)
    shutil.copyfile(work / "inputs/newc22", local / "newc22")
    platform_source = work / "checkers/platform_requirements.cpp"
    platform_source.write_text(
        'static_assert(sizeof(long) == 8, "64-bit long is required");\n'
        'static_assert(((-1L) >> 1) == -1, "Arithmetic signed right shift is required");\n'
        'static_assert(sizeof(__int128) == 16, "128-bit integer support is required");\n'
    )
    run("compiler-platform-preflight", cxx +
        ["-std=c++17", "-fsyntax-only", str(platform_source)])
    if not args.reuse_charts:
        gmp_cflags = (shlex.split(args.gmp_cflags) if args.gmp_cflags is not None
                      else pkg_config("--cflags") or [])
        gmp_libs = (shlex.split(args.gmp_libs) if args.gmp_libs is not None
                    else pkg_config("--libs") or ["-lgmpxx", "-lgmp"])
        if any(flag.startswith("-DNDEBUG") for flag in gmp_cflags):
            raise RuntimeError("GMP flags must not disable assertions")
        run("compile-chart", cxx + ["-std=c++17", "-O3"] + gmp_cflags +
            [str(chart_dir / "chart_gmp.cpp")] + gmp_libs +
            ["-o", str(chart_dir / "chart_gmp")])
    for name, (degree, bits, expected) in CHARTS.items():
        path = chart_dir / name
        if args.reuse_charts:
            shutil.copyfile(checked_package_file("inputs/" + name, hashes), path)
        else:
            run("generate-" + name, [chart_dir / "chart_gmp", degree, bits, path])
        if digest(path) != expected:
            raise RuntimeError("Chart differs from the reference SHA-256: " + name)
    shutil.copyfile(chart_dir / "qP420_gmp", local / "qP")

    # Call the unchanged certify function, parameterized for each chart's N and Q.
    norm_code = '''import runpy,sys
from pathlib import Path
d=runpy.run_path(sys.argv[1]); n,q=map(int,sys.argv[3:])
f=d['certify']; f.__globals__.update(N=n,Q=1<<q)
v=iter(map(int,Path(sys.argv[2]).read_text().split()))
p=[[next(v) for _ in range(k+1)] for k in range(n+1)]
assert next(v,None) is None
assert all(row==row[::-1] for row in p)
f(p)
print('pgen.certify PASS',n,q)
'''
    pgen = work / "checkers/pgen.py"
    for name, (degree, bits, _) in CHARTS.items():
        run("norms-" + name, [sys.executable, "-c", norm_code, pgen,
                              chart_dir / name, degree, bits])
    common = cxx + ["-std=c++17", "-O2", "-fsanitize=undefined", "-fno-sanitize-recover=all"]
    # Finite support examples supplement the general tensor-policy proof.
    tensor_checker = work / "checkers/check_tensor_primitives"
    run("compile-tensor-primitives", common +
        [str(work / "checkers/check_tensor_primitives.cpp"), "-o", str(tensor_checker)])
    run("tensor-primitives", [tensor_checker])
    run("compile-hcheck", common + ["-DHON", "ib.cpp", "-o", "hcheck"], cwd=local)
    run("compile-bcheck", common + ["ib.cpp", "-o", "bcheck"], cwd=local)
    run("generate-boundary-data", [sys.executable, "gen.py"], cwd=local, log=local / "gen.log")
    run("hcheck", [local / "hcheck"], cwd=local, log=local / "hcheck.log")
    run("bcheck", [local / "bcheck", "0", "65536"], cwd=local, log=local / "bcheck.log")
    run("interior-final", [sys.executable, local / "run_interior.py"],
        cwd=local, log=local / "interior-final.log")
    run("geometry", [sys.executable, chart_dir / "geometry/pgeo.py", "0", "480"])
    run("exact-chart-certificate", [sys.executable, chart_dir / "certify_chart.py",
                                    chart_dir / "qP780_gmp", "780", "500"])
    run("recorded-bounds", [sys.executable, chart_dir / "verify_recorded_bounds.py"])
    run("summary", [sys.executable, local / "verify_summary.py"])
    print("All numerical stages passed. Mathematical lemmas require separate review.")
    print("Summary:", local / "verification-summary.json")
    print("Commands and source substitutions:", work / "driver-provenance.json")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError, KeyError) as error:
        print("Reproduction failed:", error, file=sys.stderr)
        raise SystemExit(1)
