"""Run one twist of the exact source thermal calculation and retain evidence.

The mathematical implementation is imported unchanged from thermal.py.
This wrapper adds timing, exact interval records and comparison to supplied
output. It does not replace any arithmetic in part().
"""
import argparse
from datetime import datetime, timezone
from fractions import Fraction as F
from hashlib import sha256
import json
from math import factorial
from pathlib import Path
import platform
import sys
import time

import thermal


def ratio(x):
    return {"numerator": x.numerator, "denominator": x.denominator}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--twist", type=int, required=True, choices=(0, 1, 2))
    args = parser.parse_args()
    base = Path(__file__).resolve().parent
    out = base / "runs"
    out.mkdir(exist_ok=True)
    expected = [int(x) for x in (base / "thermal-expected.txt").read_text().split()]
    centers = [[8945303, 346734, 939987],
               [3741281, 567167, 984108],
               [2327547, 721090, 1002613]]
    print(json.dumps({"event": "start", "twist": args.twist,
                      "utc": datetime.now(timezone.utc).isoformat(),
                      "python": sys.version, "platform": platform.platform(),
                      "thermal_sha256": sha256((base / "thermal.py").read_bytes()).hexdigest(),
                      "wrapper_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
                      "retained_coefficients": len(thermal.probs)}), flush=True)
    for row, n in enumerate((6, 8, 10)):
        started = time.perf_counter()
        cpu = time.process_time()
        print(json.dumps({"event": "case-start", "n": n, "twist": args.twist}), flush=True)
        total = thermal.part(n, args.twist)
        x = F(1500000 - 1401482, 10**6) * F(21*n, 2)
        lo = sum(x**j / factorial(j) for j in range(101))
        hi = lo + 2*x**101 / factorial(101)
        lower, upper = lo * total / thermal.Q**2, hi * total / thermal.Q**2
        center = F(centers[row][args.twist], 10**6)
        assert lower > center - F(2, 10**6)
        assert upper < center + F(2, 10**6)
        assert total == expected[3*row + args.twist]
        error = 3**6 * 243 * (F(257*(2*243+1), thermal.Q) + F(1, 2**116))
        assert upper < 16
        assert error < F(4, 10**7)
        trace_error = (8+error)*error
        assert F(2, 10**6)+trace_error < F(1, 10**5)
        result = {"n": n, "twist": args.twist, "total": total,
                  "source_output_matches": True, "source_assertions_pass": True,
                  "elapsed_seconds": time.perf_counter()-started,
                  "cpu_seconds": time.process_time()-cpu,
                  "utc": datetime.now(timezone.utc).isoformat(),
                  "center": ratio(center), "computed_trace_lower": ratio(lower),
                  "computed_trace_upper": ratio(upper),
                  "scaled_frobenius_error_bound": ratio(error),
                  "trace_error_bound": ratio(trace_error),
                  "true_trace_lower": ratio(lower-trace_error),
                  "true_trace_upper": ratio(upper+trace_error)}
        (out / f"n{n}-g{args.twist}.json").write_text(json.dumps(result, indent=2)+"\n")
        print(json.dumps({"event": "case-pass", "n": n, "twist": args.twist,
                          "total": total, "elapsed_seconds": result["elapsed_seconds"],
                          "cpu_seconds": result["cpu_seconds"]}), flush=True)
    print(json.dumps({"event": "all-pass", "twist": args.twist}), flush=True)


if __name__ == "__main__":
    main()
