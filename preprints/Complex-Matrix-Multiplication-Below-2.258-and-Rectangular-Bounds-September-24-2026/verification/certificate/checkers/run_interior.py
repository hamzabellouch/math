"""Run the reviewed polynomial checker on every angular sector locally."""
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from pathlib import Path
import hashlib
import json
from math import comb, factorial
import multiprocessing
import runpy
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
DEST = HERE / "interior-final"
DEST.mkdir(exist_ok=True)
(DEST / "cells").mkdir(exist_ok=True)
src = ROOT / "source/dynamic-edit-recovery/full-cat"
generator = (src / "rooLS.py").read_text()
generator = generator.replace("'/tmp/newc22'", repr(str(HERE / "newc22")))
generator = generator.replace("'/tmp/qP'", repr(str(HERE / "qP")))
(DEST / "generator.py").write_text(generator)
checker = (src / "rooLS.cpp").read_text()
(DEST / "checker.cpp").write_text(checker)
subprocess.run(["clang++", "-std=c++17", "-O2", "-fsanitize=undefined",
                "-fno-sanitize-recover=all", str(DEST / "checker.cpp"),
                "-o", str(DEST / "checker")], check=True)
mod = runpy.run_path(str(DEST / "generator.py"))
# Exact version of the added truncation assertions recovered at trace399673.
U, N, J = mod["U"], mod["N"], mod["J"]
pi_upper = Fraction(22, 7)
for row in mod["allf"]:
    for _, polynomial in row:
        values = [(i+j, Fraction(abs(v), U)) for (i,j),v in polynomial.items()]
        assert all(k < 320 for k,_ in values)
        assert sum(v for _,v in values) < 1 << 36
        m = J + 1
        bound = sum(v * ((k*pi_upper/(6*N))**m / factorial(m)
                         + 4*Fraction(comb(k,m), (2*N)**m)) for k,v in values)
        assert bound < Fraction(1, 10**10), ("Taylor bound", bound)
print("exact angular/radial truncation assertions PASS", flush=True)

def check_sector(sector):
    rows = [f'{mod["T"]} {N} {J} {len(mod["allf"])}']
    for i, row in enumerate(mod["allf"]):
        matrix = mod["series"](row, sector, i == 4)
        rows.append(str(len(matrix)))
        rows.extend(" ".join(map(str, line)) for line in matrix)
    data = ("\n".join(rows) + "\n").encode()
    path = DEST / "cells" / f"{sector:03d}.dat"
    path.write_bytes(data)
    result = subprocess.run([str(DEST / "checker")], input=data,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return {"sector": sector, "exit_code": result.returncode,
            "output": result.stdout.decode(), "sha256": hashlib.sha256(data).hexdigest()}

if __name__ == "__main__":
    started = time.monotonic()
    ctx = multiprocessing.get_context("fork")
    results = []
    with ProcessPoolExecutor(max_workers=4, mp_context=ctx) as executor:
        for result in executor.map(check_sector, range(N)):
            results.append(result)
            print(json.dumps(result), flush=True)
    (DEST / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    failures = [r for r in results if r["exit_code"]]
    print(json.dumps({"sectors": N, "failures": len(failures),
                      "seconds": time.monotonic() - started}), flush=True)
    if failures:
        raise SystemExit(1)
