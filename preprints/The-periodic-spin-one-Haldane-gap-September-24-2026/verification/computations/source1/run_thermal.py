#!/usr/bin/env python3
"""Execute the supplied thermal computation, partitioned by magnetization.

The inner integer algorithm and its matrix/orbit functions are loaded from
the byte-preserved prefix of the source. Independent magnetization summands
are evaluated in separate processes; exact Python-integer summation then
recovers each source raw(n, tw, 32) result.
"""
import argparse
import concurrent.futures
import hashlib
import itertools
import json
import os
from pathlib import Path
import platform
import runpy
import time

import numpy as np
import scipy

HERE = Path(__file__).resolve().parent
SRC = runpy.run_path(str(HERE / "thermal-definitions.py"))


def sector(task):
    n, tw, magnetization = task
    started = time.perf_counter()
    cpu_started = time.process_time()
    words = [w for w in itertools.product((-1, 0, 1), repeat=n)
             if sum(w) == magnetization]
    D = SRC["dmat"](words, tw)
    assert D.dtype == np.int64
    assert (D - D.T).nnz == 0
    row_bound = abs(32 - 3*n) + 6*n
    actual_row_bound = int(abs(D).sum(axis=1).max())
    assert actual_row_bound <= row_bound <= 76
    rows, mult = SRC["reps"](words)
    total = 0
    for j in range(0, len(rows), 32):
        rr = rows[j:j+32]
        idx = rr, list(range(len(rr)))
        X = np.zeros((len(words), len(rr)), dtype=np.int64)
        for ck in reversed(SRC["cc"]):
            X = (D @ X)//32
            X[idx] += ck
        assert max(abs(int(X.min())), abs(int(X.max()))) < 2*SRC["Q"]
        sq = (X.astype(object)**2).sum(axis=0)
        total += sum(x*m for x, m in zip(sq, mult[j:j+32]))
    return {
        "n": n, "tw": tw, "magnetization": magnetization,
        "dimension": len(words), "representatives": len(rows),
        "column_multiplicity": sum(mult),
        "row_absolute_sum_max": actual_row_bound,
        "row_absolute_sum_bound": row_bound,
        "W": str(int(total)),
        "wall_seconds": time.perf_counter()-started,
        "cpu_seconds": time.process_time()-cpu_started,
    }


def certify(n, tw, W):
    """The source therm() interval check, with exact bounds recorded."""
    from fractions import Fraction as F
    from math import isqrt
    sl, sh = SRC["scale"](n)
    d = isqrt(3**n)+1
    err = d*((SRC["J"]+1)*(d+1)+1)
    r = isqrt(W)
    lo = sl*F(max(0, r-err)**2, SRC["Q"]**2)
    hi = sh*F((r+1+err)**2, SRC["Q"]**2)
    center = F(SRC["table"][n-4][tw], 10**6)
    assert lo > center-SRC["eps"] and hi < center+SRC["eps"]
    return {"n": n, "tw": tw, "W": str(W), "center": str(center),
            "allowed_error": str(SRC["eps"]),
            "lower": str(lo), "upper": str(hi),
            "lower_margin": str(lo-(center-SRC["eps"])),
            "upper_margin": str(center+SRC["eps"]-hi),
            "d": d, "frobenius_error_units": err}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--min-n", type=int, default=4)
    parser.add_argument("--max-n", type=int, default=12)
    parser.add_argument("--output", type=Path, default=HERE / "thermal-run")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    expected = {}
    for line in (HERE / "source-output.txt").read_text().splitlines()[:18]:
        n, tw, W = map(int, line.split())
        expected[n, tw] = W
    metadata = {
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "python": platform.python_version(), "numpy": np.__version__,
        "scipy": scipy.__version__, "platform": platform.platform(),
        "cpu_count": os.cpu_count(), "workers": args.workers,
        "assertions_enabled": __debug__,
        "hashes": {name: hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                   for name in ("original-computation.py", "thermal-definitions.py",
                                "source-output.txt", "run_thermal.py")}}
    assert __debug__
    (args.output / "metadata.json").write_text(json.dumps(metadata, indent=2)+"\n")
    tasks = [(n, tw, M) for n in range(args.min_n, args.max_n+1)
             for tw in range(2) for M in range(n+1)]
    # Largest magnetization blocks begin first, avoiding a long final queue.
    tasks.sort(key=lambda t: (-t[0], t[2], t[1]))
    received = {}
    totals = {}
    certificates = []
    start = time.perf_counter()
    cpu = 0.0
    with (args.output / "sectors.jsonl").open("w") as records:
        with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
            futures = [pool.submit(sector, task) for task in tasks]
            for future in concurrent.futures.as_completed(futures):
                result = future.result()
                records.write(json.dumps(result, sort_keys=True)+"\n")
                records.flush()
                cpu += result["cpu_seconds"]
                key = result["n"], result["tw"]
                received[key] = received.get(key, 0)+1
                totals[key] = totals.get(key, 0)+int(result["W"])
                print("sector", result["n"], result["tw"], result["magnetization"],
                      "done", round(result["wall_seconds"], 3), flush=True)
                if received[key] == key[0]+1:
                    assert totals[key] == expected[key], (key, totals[key], expected[key])
                    certificate = certify(*key, totals[key])
                    certificates.append(certificate)
                    print("certified", *key, totals[key], flush=True)
    certificates.sort(key=lambda r: (r["n"], r["tw"]))
    (args.output / "certificates.json").write_text(json.dumps(certificates, indent=2)+"\n")
    (args.output / "outputs.txt").write_text("".join(
        f'{r["n"]} {r["tw"]} {r["W"]}\n' for r in certificates))
    metadata.update({"finished_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                     "wall_seconds": time.perf_counter()-start,
                     "worker_cpu_seconds": cpu, "certificates": len(certificates),
                     "all_source_outputs_match": True, "all_intervals_pass": True})
    (args.output / "metadata.json").write_text(json.dumps(metadata, indent=2)+"\n")
    print("PASS", len(certificates), "thermal intervals; all exact source outputs match", flush=True)


if __name__ == "__main__":
    main()
