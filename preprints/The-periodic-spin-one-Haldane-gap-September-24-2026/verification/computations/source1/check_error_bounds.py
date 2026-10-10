#!/usr/bin/env python3
"""Exact scalar checks for the 72-site initialization's thermal algorithm."""
from fractions import Fraction
import hashlib
import json
from math import factorial, isqrt
from pathlib import Path
import runpy

HERE = Path(__file__).resolve().parent
s = runpy.run_path(str(HERE / "thermal-definitions.py"))
Q, J = s["Q"], s["J"]
assert Q == 2**55 and J == 280
assert 98**281 < factorial(281)
# Tail ratio 98/(281+1) < 1/2; e>2 gives conditioned error <2^-96.
assert Fraction(98, 282) < Fraction(1, 2)
conditioned_error_bound = Fraction(1, 2**96)
assert conditioned_error_bound < Fraction(1, Q)
assert all(x >= 0 for x in s["c"]) and sum(s["c"]) <= Q
assert s["m"] == 191 and len(s["cc"]) == 192
rows = []
for n in range(4, 13):
    dimension = 3**n
    d = isqrt(dimension)+1
    assert d*d > dimension
    suffix_rounding_bound = (J+1)*(d+1)
    prior_coordinate_bound = Q+suffix_rounding_bound
    assert prior_coordinate_bound < 2*Q
    row_sum_bound = abs(32-3*n)+6*n
    assert row_sum_bound <= 76
    numerator_bound = row_sum_bound*2*Q
    assert numerator_bound < 2**63
    post_addition_bound = (numerator_bound+31)//32+Q
    assert post_addition_bound < 2**63
    x = s["b0"]*n*(Fraction(3, 2)-s["a0"])
    assert 0 <= x < 15
    assert x/(101-x) < 1
    lo, hi = s["scale"](n)
    assert 0 < lo < hi
    rows.append({
        "n": n, "full_dimension": dimension, "d": d,
        "rounding_bound_Q_units": suffix_rounding_bound,
        "column_error_Q_units": suffix_rounding_bound+1,
        "frobenius_error_Q_units": d*(suffix_rounding_bound+1),
        "prior_coordinate_bound": prior_coordinate_bound,
        "row_absolute_sum_bound": row_sum_bound,
        "sparse_partial_sum_bound": numerator_bound,
        "division_and_addition_bound": post_addition_bound,
        "scale_exponent": str(x),
    })
record = {
    "assertions_enabled": __debug__,
    "Q": Q, "J": J, "last_nonzero_floored_coefficient": s["m"],
    "conditioned_operator_error_strict_upper_bound": str(conditioned_error_bound),
    "integer_maximum": 2**63-1, "bounds": rows,
    "files": {name: hashlib.sha256((HERE/name).read_bytes()).hexdigest()
              for name in ("thermal-definitions.py", "check_error_bounds.py")},
    "all_checks_pass": True,
}
assert __debug__
(HERE / "error-bounds.json").write_text(json.dumps(record, indent=2)+"\n")
print("PASS: exact Poisson, coefficient, rounding, int64 and exponential-scale bounds")
print("maximum sparse partial-sum absolute bound:", max(r["sparse_partial_sum_bound"] for r in rows))
print("maximum column error in Q units:", max(r["column_error_Q_units"] for r in rows))
print("maximum Frobenius error in Q units:", max(r["frobenius_error_Q_units"] for r in rows))
