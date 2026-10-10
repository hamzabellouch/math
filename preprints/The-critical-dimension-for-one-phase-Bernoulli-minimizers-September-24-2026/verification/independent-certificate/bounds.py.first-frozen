"""Exact interior magnitude bounds, independently transcribed from the statement.

The only mathematical source is input.md, lines 1--1124.  This module does not
import the submitted checker, graph expansion code, previous audit code, or any
expected counts or sums.  It accepts the collected rational polynomial as data.

Key convention: (g_power, w_power, z_power, traces, edges), where each edge is
(u, v, A_power), 5 denotes p, 6 denotes ell, and 7/8 denote copies of X.
The magnitude order is (|w|, |z|, |ell|, |X|), numbered 1 through 4 in output.
"""

from fractions import Fraction
from math import isqrt


Q = 250000
ROUNDING_SCALE = 100000
MATRIX_SCALE = 2 * ROUNDING_SCALE * Q * Q
THETA = Fraction(4, 5)
PAIR_ORDER = tuple((i, j) for i in range(1, 5) for j in range(i, 5))


def rational_json(value):
    """Use integer numerator/denominator fields, without a float conversion."""
    value = Fraction(value)
    return {"numerator": value.numerator, "denominator": value.denominator}


def ceil_scaled_sqrt(squared, scale=ROUNDING_SCALE):
    """Return the least n >= scale*sqrt(squared), using integer arithmetic."""
    squared = Fraction(squared)
    if squared < 0 or not isinstance(scale, int) or scale < 0:
        raise ValueError("The squared bound and integer scale must be nonnegative")
    numerator = squared.numerator * scale * scale
    denominator = squared.denominator
    lower = isqrt(numerator // denominator)
    return lower + (lower * lower * denominator < numerator)


def key_factors(key):
    """Derive the magnitude pair and L_t^2 directly from one collected key."""
    h, w_power, z_power, traces, edges = key
    assert all(isinstance(v, int) and v >= 0 for v in (h, w_power, z_power))
    assert isinstance(traces, tuple) and tuple(sorted(traces)) == traces
    assert isinstance(edges, tuple) and tuple(sorted(edges)) == edges
    assert all(isinstance(k, int) and k >= 3 for k in traces)

    endpoint_counts = {5: 0, 6: 0, 7: 0, 8: 0}
    squared = Fraction(1)
    for power in traces:
        squared *= Fraction(9, 20) if power == 3 else THETA ** (power - 2)

    for u, v, power in edges:
        assert u in endpoint_counts and v in endpoint_counts, "Free endpoint in scalar key"
        assert u <= v and isinstance(power, int) and power >= 0
        endpoint_counts[u] += 1
        endpoint_counts[v] += 1
        if u == v and u in (7, 8):
            # A metric joining two slots of one trace-free X must be discarded
            # when collecting the polynomial, before this bound is applied.
            assert power >= 1, "Nonzero key contains a trace-free X metric contraction"
            squared *= Fraction(5, 7) if power == 1 else THETA ** (power - 1)
        else:
            squared *= THETA ** power

    x_copies = sum(endpoint_counts[x] > 0 for x in (7, 8))
    assert all(endpoint_counts[x] in (0, 3) for x in (7, 8)), "Each X has three slots"
    p_count = endpoint_counts[5]
    ell_count = endpoint_counts[6]
    if h > 0 and p_count > 0:
        squared *= Fraction(h, h + p_count) ** h
        squared *= Fraction(p_count, h + p_count) ** p_count

    magnitudes = (1,) * w_power + (2,) * z_power + (3,) * ell_count + (4,) * x_copies
    assert len(magnitudes) == 2, "Collected interior key must have magnitude degree two"
    assert squared > 0
    return magnitudes, squared


def summarize(coefficients):
    """Accumulate all nonzero keys into the ten exact scaled matrix entries.

    Input values are actual rational coefficients of E, not integer numerators.
    Each value must have denominator dividing Q^2.  The output is entirely JSON
    compatible.  `pairs` is ordered 11,12,13,14,22,23,24,33,34,44 and records the
    entries of 2*100000*Q^2*D0.  `per_key` provides every factor bound and upward
    rounded integer, so the accumulation can be reproduced without this code.
    """
    pair_counts = {pair: 0 for pair in PAIR_ORDER}
    pair_scaled_entries = {pair: 0 for pair in PAIR_ORDER}
    per_key = []
    for key, coefficient in sorted(coefficients.items()):
        coefficient = Fraction(coefficient)
        if coefficient == 0:
            continue
        pair, squared = key_factors(key)
        rounded = ceil_scaled_sqrt(squared)
        scaled_coefficient = abs(coefficient) * Q * Q
        assert scaled_coefficient.denominator == 1, "Coefficient denominator does not divide Q^2"
        # Off-diagonal D0 entries receive half the coefficient bound; the
        # overall scale's factor two cancels that half.  Diagonal entries
        # receive the full bound and therefore retain that factor two.
        scaled_contribution = scaled_coefficient.numerator * rounded
        if pair[0] == pair[1]:
            scaled_contribution *= 2
        pair_counts[pair] += 1
        pair_scaled_entries[pair] += scaled_contribution
        h, w_power, z_power, traces, edges = key
        per_key.append({
            "key": [h, w_power, z_power, list(traces), [list(edge) for edge in edges]],
            "pair": list(pair),
            "coefficient": rational_json(coefficient),
            "L2": rational_json(squared),
            "integerceil": rounded,
            "scaled_contribution": scaled_contribution,
        })
    return {
        "Q": Q,
        "rounding_scale": ROUNDING_SCALE,
        "matrix_scale": MATRIX_SCALE,
        "nonzero_key_count": len(per_key),
        "pairs": [
            {"pair": list(pair), "count": pair_counts[pair], "scaled_entry": pair_scaled_entries[pair]}
            for pair in PAIR_ORDER
        ],
        "per_key": per_key,
    }


def self_check():
    """Small independently transparent cases; no certificate totals are used."""
    assert ceil_scaled_sqrt(0) == 0
    assert ceil_scaled_sqrt(1) == 100000
    assert ceil_scaled_sqrt(Fraction(1, 4)) == 50000
    assert ceil_scaled_sqrt(Fraction(4, 9), scale=3) == 2
    assert ceil_scaled_sqrt(Fraction(399, 100), scale=1) == 2
    assert ceil_scaled_sqrt(Fraction(401, 100), scale=1) == 3

    ww = (0, 2, 0, (), ())
    assert key_factors(ww) == ((1, 1), Fraction(1))
    # Cubic trace and fourth-power trace contribute (9/20)*(4/5)^2.
    assert key_factors((0, 0, 2, (3, 4), ())) == ((2, 2), Fraction(36, 125))
    # g^2 |p|^2 |ell|^2 has mixed factor (2/4)^2*(2/4)^2.
    assert key_factors((2, 0, 0, (), ((5, 5, 0), (6, 6, 0)))) == ((3, 3), Fraction(1, 16))
    # g^2 w p.A^2.p z multiplies the mixed factor by theta^2.
    assert key_factors((2, 1, 1, (), ((5, 5, 2),))) == ((1, 2), Fraction(1, 25))
    # ell contracted with X:A uses the stated 5/7 improvement.
    assert key_factors((0, 0, 0, (), ((6, 7, 0), (7, 7, 1)))) == ((3, 4), Fraction(5, 7))
    # The same-copy A^2 edge uses theta^(2-1).
    assert key_factors((0, 1, 0, (), ((5, 7, 0), (7, 7, 2)))) == ((1, 4), Fraction(4, 5))
    # Three edges between distinct X copies use operator powers separately.
    xx = (0, 0, 0, (), ((7, 8, 0), (7, 8, 1), (7, 8, 2)))
    assert key_factors(xx) == ((4, 4), Fraction(64, 125))

    wz = (0, 1, 1, (), ())
    example = summarize({ww: Fraction(3, Q * Q), wz: Fraction(-7, Q * Q), xx: Fraction(0)})
    assert example["nonzero_key_count"] == 2
    assert example["pairs"][0] == {"pair": [1, 1], "count": 1, "scaled_entry": 600000}
    assert example["pairs"][1] == {"pair": [1, 2], "count": 1, "scaled_entry": 700000}
    assert all(row["count"] == 0 and row["scaled_entry"] == 0 for row in example["pairs"][2:])


if __name__ == "__main__":
    self_check()
    print("Exact magnitude bound self-checks passed.")
