"""Independent exact checks of the thermal matrix formulas and error constants.

These finite checks supplement the general identities in the arithmetic audit.
They do not replace the three full-size thermal runs.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
import json
from math import factorial
from pathlib import Path


def add(a, b):
    return a[0]+b[0], a[1]+b[1]


def mul(a, b):
    u, v = a
    x, y = b
    return u*x-v*y, u*y+v*x-v*y


def conj(a):
    return a[0]-a[1], -a[1]


def phase(g, k):
    if g == 0:
        return 1, 0
    if g == 1:
        return (-1 if k % 2 else 1), 0
    return ((1, 0), (0, 1), (-1, -1))[k % 3]


def physical_hamiltonian(n, g):
    # Build by applying the two ladder terms to each COLUMN word.
    matrix = {}
    for y in product((-1, 0, 1), repeat=n):
        matrix[y, y] = sum(y[j-1]*y[j] for j in range(n)), 0
        for j in range(n):
            k = (j+1) % n
            for step in (-1, 1):
                x = list(y)
                x[j] += step
                x[k] -= step
                if abs(x[j]) > 1 or abs(x[k]) > 1:
                    continue
                x = tuple(x)
                # Conjugation by exp(-i theta Sz) on site 0 at the seam.
                value = phase(g, y[0]-x[0]) if k == 0 else (1, 0)
                matrix[x, y] = add(matrix.get((x, y), (0, 0)), value)
    return matrix


def source_numerator(n, g):
    # Independently expose the row-adjacency rules used inside thermal.part.
    matrix = {}
    for x in product((-1, 0, 1), repeat=n):
        matrix[x, x] = 16-3*n//2-sum(x[j-1]*x[j] for j in range(n)), 0
        for j in range(n):
            k = (j+1) % n
            for delta in (-1, 1):
                y = list(x)
                y[j] -= delta
                y[k] += delta
                if abs(y[j]) > 1 or abs(y[k]) > 1:
                    continue
                y = tuple(y)
                value = mul((-1, 0), phase(g, delta if k == 0 else 0))
                matrix[x, y] = add(matrix.get((x, y), (0, 0)), value)
    return matrix


def check_matrices():
    records = []
    for n in (4, 6):
        for g in range(3):
            h = physical_hamiltonian(n, g)
            b = source_numerator(n, g)
            assert h.keys() == b.keys()
            for (x, y), value in h.items():
                expected = add(mul((-1, 0), value), (16-3*n//2, 0) if x == y else (0, 0))
                assert b[x, y] == expected
                assert value == conj(h[y, x])
                assert sum(x) == sum(y)
                rx, ry = x[::-1], y[::-1]
                fx, fy = tuple(-s for s in x), tuple(-s for s in y)
                assert h[rx, ry] == conj(value)
                assert h[fx, fy] == conj(value)
                sx, sy = (x[-1],)+x[:-1], (y[-1],)+y[:-1]
                transported = mul(mul(phase(g, -x[-1]), value), phase(g, y[-1]))
                assert h[sx, sy] == transported
            records.append({"n": n, "twist": g, "dimension": 3**n,
                            "entries_checked": len(h), "matrix_and_symmetry_checks": "pass"})
    return records


def check_triad():
    def weight(x):
        if x[0] == x[1] == x[2]:
            return 4
        if x[0] == x[1] or x[1] == x[2]:
            return 3
        return 2
    results = []
    for x in product(range(3), repeat=3):
        row = defaultdict(int)
        for j in (0, 1):
            k = j+1
            if x[j] == x[k]:
                for s in range(3):
                    if s != x[j]:
                        y = list(x)
                        y[j] = y[k] = s
                        row[tuple(y)] += 1
            else:
                y = list(x)
                y[j], y[k] = y[k], y[j]
                row[tuple(y)] -= 1
        row_bound = sum(abs(v)*weight(y) for y, v in row.items())
        assert row_bound <= 3*weight(x)
        results.append({"word": x, "weight": weight(x), "weighted_row_sum": row_bound})
    return results


def main():
    q = 2**56
    error = 257*(2*243+1)
    assert 32*(q+error) < 2**63  # stronger rational substitute for 32/sqrt(3)
    assert 2*(q+error) < 2**63
    assert 27**28 < 32**28
    delta = 3**6*243*(F(error, q)+F(1, 2**116))
    assert delta < F(4, 10**7)
    trace_error = (8+delta)*delta
    assert trace_error+F(2, 10**6) < F(1, 10**5)
    exponent_records = []
    for n in (6, 8, 10):
        x = F(98518, 10**6)*F(21*n, 2)
        assert 0 <= x < 12
        assert x/F(102) < F(1, 2)
        # Hence the omitted Taylor tail is at most twice its first term.
        exponent_records.append({"n": n, "scale_exponent": str(x),
                                 "half_exponent_lt_6": x/2 < 6})
    result = {"matrices": check_matrices(), "triad": check_triad(),
              "largest_horner_column_error": error,
              "lane_numerator_bound": 32*(q+error),
              "lane_limit": 2**63,
              "scaled_norm_error": str(delta),
              "total_trace_error_including_center": str(trace_error+F(2, 10**6)),
              "scale_exponents": exponent_records, "all_checks": "pass"}
    path = Path(__file__).resolve().parent / "runs" / "independent-arithmetic.json"
    path.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"all_checks": "pass", "output": str(path),
                      "matrix_entries_checked": sum(x["entries_checked"] for x in result["matrices"]),
                      "triad_rows_checked": len(result["triad"])}))


if __name__ == "__main__":
    main()
