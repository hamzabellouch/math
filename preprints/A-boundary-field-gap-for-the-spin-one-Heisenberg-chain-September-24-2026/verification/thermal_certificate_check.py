#!/usr/bin/env python3
"""Fresh implementation of thermal.tex; not the missing historical verifier.

Exact sparse integer Horner recurrence, exact rational error enclosures.
NumPy/SciPy int64 arithmetic is used only under the documented overflow bound.
No eigensolver or floating-point arithmetic enters any certificate decision.
"""
from fractions import Fraction as F
from math import factorial, isqrt
from pathlib import Path
import hashlib
import json
import platform
import sys
import time

if not __debug__:
    raise SystemExit('Do not run with -O or PYTHONOPTIMIZE: exact certificate assertions must remain enabled.')

import numpy as np
import scipy
from scipy.sparse import csr_matrix

K, Q = 192, 2**50
A_SHIFT, BETA = F(700741, 500000), F(49, 4)
EXPECTED = {
    2: (10185296075298, 4160017987, 583578389575),
    3: (259254948723, 571111660440989, 47796720049308),
    4: (318278534893, 661347985, 43971049724),
    5: (260908126900, 29917222640283, 5659378873682),
    6: (16467340956, 328219854, 4086161507),
}


def exp_interval(y):
    """Equation appth:scalar-exp, including reciprocal rule."""
    if y < 0:
        lo, hi = exp_interval(-y)
        return 1 / hi, 1 / lo
    assert 0 <= y <= 10
    term = F(1)
    total = term
    for j in range(1, 81):
        term *= y / j
        total += term
    return total, total + 2 * term * y / 81


def decimal_enclosure(x, digits=14):
    """Display only: bracket an exact fraction between decimal multiples."""
    p = 10**digits
    n = x.numerator * p // x.denominator
    return [str(F(n, p)), str(F(n + 1, p))]


def word(number, n):
    return tuple(number // 3**j % 3 - 1 for j in range(n))


def number(w):
    return sum((v + 1) * 3**j for j, v in enumerate(w))


def integer_matrix(n, g):
    """Direct construction of appth:diagonal and appth:scalar."""
    d = 3**n
    words = [word(i, n) for i in range(d)]
    parity = [sum(w) % 2 for w in words]
    c10 = 30 * ((n - 1) // 2) + 20 * ((n - 1) % 2) + 12
    rows, cols, data = [], [], []
    for i, w in enumerate(words):
        entries = {
            i: 80 - c10 - 10 * sum(w[j] * w[j + 1] for j in range(n - 1))
            + 6 * w[0] - 6 * g * w[-1]
        }
        for j in range(n - 1):
            for sign in (-1, 1):
                v = list(w)
                v[j] += sign
                v[j + 1] -= sign
                if -1 <= v[j] <= 1 and -1 <= v[j + 1] <= 1:
                    k = number(v)
                    assert k not in entries
                    entries[k] = -10
        if g == 0:
            for sign in (-1, 1):
                v = list(w)
                v[-1] += sign
                if -1 <= v[-1] <= 1:
                    k = number(v)
                    assert k not in entries
                    entries[k] = -3 * (1 + parity[i])
        for j, entry in sorted(entries.items()):
            rows.append(i)
            cols.append(j)
            data.append(entry)
    matrix = csr_matrix((np.array(data, dtype=np.int64), (rows, cols)), shape=(d, d))
    # After inverse similarity, this must be exactly self-adjoint.
    coo = matrix.tocoo()
    for i, j, v in zip(coo.row, coo.col, coo.data):
        assert int(v) * (1 + parity[j]) == int(matrix[j, i]) * (1 + parity[i])
    row_bound = int(abs(matrix).sum(axis=1).max())
    assert row_bound <= 120
    return matrix, parity, c10, row_bound


def certify(n, g, expected, coefficients):
    start = time.monotonic()
    matrix, parity, c10, row_bound = integer_matrix(n, g)
    d = 3**n
    # The ideal normalized coefficient polynomial has max entry <=sqrt(2)*Q.
    # Each stage's entrywise floor and scalar coefficient floor, propagated
    # through J A^r J^-1, contribute at most sqrt(2)*(d+1)<=2*d (d>=9).
    # Across <=193 stages, X entries therefore stay strictly below 2Q.
    assert F(3, 2) * Q + 2 * (K + 1) * d < 2 * Q
    assert row_bound * 2 * Q < 2**63 - 1
    x = np.zeros((d, d), dtype=np.int64)
    largest_x = largest_product = 0
    stages = []
    diag = np.diag_indices(d)
    for i in range(K, -1, -1):
        # The preceding rigorous bound applies BEFORE this fixed-width product.
        assert int(abs(x).max()) < 2 * Q
        product = matrix @ x
        largest_product = max(largest_product, int(abs(product).max()))
        x = product // 80
        x[diag] += coefficients[i]
        bound = int(abs(x).max())
        largest_x = max(largest_x, bound)
        assert bound < 2 * Q
        stages.append({"i": i, "max_abs_x": bound})
    # Python ints, not int64, for all squares and accumulated sums.
    numerator = sum(
        int(x[i, j])**2 * (2 - parity[i]) * (1 + parity[j])
        for i in range(d) for j in range(d)
    )
    quotient = 10**16 * numerator // (2 * Q**2)
    assert quotient == expected, (n, g, quotient, expected)
    lower, upper = F(quotient, 10**16), F(quotient + 1, 10**16)
    root_bound = F(isqrt(quotient + 1) + 1, 10**8)
    error = F(4, 10**10) * root_bound + F(4, 10**20)
    assert lower - error > 0
    exponent = BETA * (F(c10, 10) - A_SHIFT * n)
    exp_lo, exp_hi = exp_interval(exponent)
    interval = (exp_lo * (lower - error), exp_hi * (upper + error))
    record = {
        "n": n, "g": g, "dimension": d, "c10": c10,
        "matrix_nonzero_entries": matrix.nnz,
        "max_abs_row_sum": row_bound, "max_abs_x": largest_x,
        "max_abs_product": largest_product,
        "max_product_bound": row_bound * 2 * Q,
        "weighted_square_numerator": str(numerator),
        "weighted_square_denominator": str(2 * Q**2),
        "quotient": quotient, "printed_quotient_matches": True,
        "matrix_sha256": hashlib.sha256(matrix.toarray().astype('<i8').tobytes()).hexdigest(),
        "final_x_sha256": hashlib.sha256(x.astype('<i8').tobytes()).hexdigest(),
        "exponent": str(exponent), "thermal_interval": list(map(str, interval)),
        "thermal_lower_display": decimal_enclosure(interval[0]),
        "thermal_upper_display": decimal_enclosure(interval[1]),
        "stages": stages, "seconds": time.monotonic() - start,
    }
    return record, interval


def main():
    start = time.monotonic()
    p = [49**i * factorial(K) // factorial(i) for i in range(K + 1)]
    total = sum(p)
    coefficients = [Q * s // total for s in p]
    assert sum(coefficients) <= Q
    tail = F(49**193, factorial(193)) / (1 - F(49, 194))
    assert tail < F(3152, 10**36)
    frobenius_bound = 54 * tail + F(432513, 2**51)
    assert frobenius_bound < F(2, 10**10)
    cases, intervals = [], {}
    for n in range(2, 7):
        for g, expected in zip((1, -1, 0), EXPECTED[n]):
            record, interval = certify(n, g, expected, coefficients)
            cases.append(record)
            intervals[n, g] = interval
            print(f'n={n} g={g:+d} d={3**n} quotient={record["quotient"]} matches=True seconds={record["seconds"]:.3f}', flush=True)
    assert F('0.0266319440') < intervals[6, 1][0]
    assert intervals[6, 1][1] < F('0.0266319607') < F('0.027')
    centers = dict(zip(range(2, 7), map(F, ('0.02703074', '0.01203562', '0.01193511', '0.00931560', '0.00893272'))))
    moments = {}
    for n in range(2, 7):
        lo = (intervals[n, 1][0] + intervals[n, -1][0] + 4 * intervals[n, 0][0]) / 6
        hi = (intervals[n, 1][1] + intervals[n, -1][1] + 4 * intervals[n, 0][1]) / 6
        assert centers[n] - F(1, 10**7) < lo < hi < centers[n] + F(1, 10**7)
        moments[n] = (lo, hi)
    polynomial_coefficients = {6: F(1), 5: -F('.28'), 4: -F('.3404'), 3: F('.0504'), 2: F('.0324')}
    poly_hi = sum(c * moments[n][int(c >= 0)] for n, c in polynomial_coefficients.items())
    assert poly_hi < F('.003745')
    center_sum = sum(c * centers[n] for n, c in polynomial_coefficients.items())
    assert center_sum == F('.003744031780')
    assert center_sum + sum(abs(c) for c in polynomial_coefficients.values()) / 10**7 == F('.0037442021')
    output = {
        "provenance": "Fresh implementation of the complete printed thermal.tex recipe, not recovered historical code.",
        "implementation_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "toolchain": {"python": sys.version, "numpy": np.__version__, "scipy": scipy.__version__, "platform": platform.platform()},
        "parameters": {"K": K, "Q": Q, "coefficient_count": len(coefficients), "coefficients": coefficients},
        "tail_bound": str(tail), "frobenius_bound": str(frobenius_bound),
        "cases": cases, "moment_intervals": {str(n): list(map(str, v)) for n, v in moments.items()},
        "polynomial_upper_bound": str(poly_hi), "polynomial_upper_display": decimal_enclosure(poly_hi),
        "all_15_printed_integer_entries_match": True,
        "all_5_printed_centers_certified": True,
        "both_thermal_conclusions_certified": True,
        "seconds": time.monotonic() - start,
    }
    Path('thermal_certificate_results.json').write_text(json.dumps(output, indent=2) + '\n')
    print('All 15 exact recurrences and both thermal conclusions certified.', flush=True)


if __name__ == '__main__':
    main()
