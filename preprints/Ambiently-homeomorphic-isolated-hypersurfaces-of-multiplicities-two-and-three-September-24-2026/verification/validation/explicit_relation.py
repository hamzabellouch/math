#!/usr/bin/env python3
"""Independently verify the explicit product relation using only Python's stdlib.

No matrix, rank certificate, factor table, or relation-producing program is read.
Each of the six positive integers in every row is factored by trial division.
Run from any directory; optional positional arguments select input and output.
"""

import argparse
from collections import Counter
import hashlib
import json
from math import gcd
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def integer(value):
    require(not isinstance(value, bool), "Boolean used as integer")
    require(isinstance(value, (int, str)), "Expected integer or decimal string")
    result = int(value)
    if isinstance(value, str):
        require(str(result) == value, "Noncanonical decimal integer")
    return result


def factor(n):
    """Trial factorization; the final remaining factor is prime by construction."""
    require(n > 0, "Factorization requires a positive integer")
    original = n
    result = {}
    p = 2
    while p * p <= n:
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        if exponent:
            result[p] = exponent
        p = 3 if p == 2 else p + 2
    if n > 1:
        result[n] = result.get(n, 0) + 1
    reconstructed = 1
    for p, exponent in result.items():
        reconstructed *= p ** exponent
    require(reconstructed == original, "Factorization reconstruction failed")
    return result


def chain(D, c):
    """Return the Euclidean chain with starting normalized weight c/D."""
    result = []
    require(0 < 2 * c < D, "Starting chain weight must lie in (0,1/2)")
    while c:
        a, remainder = divmod(D, c)
        require(a >= 2 and 0 <= remainder < c, "Invalid chain step")
        require(a * c + remainder == D, "Invalid weighted degree")
        # Internal monomial is x_i^a*x_(i+1); final monomial is x_i^a.
        ordinary_degree = a + int(remainder != 0)
        require(ordinary_degree >= 3, "Unexpected quadratic chain term")
        result.append((c, a, remainder))
        c = remainder
    return result


def verify(path):
    raw = path.read_bytes()
    data = json.loads(raw)
    d = integer(data["d"])
    require(d > 1, "Invalid denominator")
    residual_d = d
    power_of_three = 0
    while residual_d % 3 == 0:
        residual_d //= 3
        power_of_three += 1
    require(residual_d == 1, "d must be a power of 3")
    rows = [(integer(row["b"]), integer(row["e"])) for row in data["relation"]]
    require(rows, "Empty relation")
    require(len({b for b, _ in rows}) == len(rows), "Repeated b")
    require(all(0 < 2 * b < d and b % 3 and e for b, e in rows),
            "Invalid support: require 0<b<d/2, 3 does not divide b, and e nonzero")

    valuation_sums = [Counter(), Counter()]
    prime_supports = [set(), set()]
    individual_prime_support = set()
    largest_integer = 0
    for b, e in rows:
        # Signs distinguish numerator from denominator; do not cancel in advance.
        groups = (((d - b, 1), (b, -1)),
                  ((2 * d + b, 1), (2 * d - b, 1),
                   (3 * d - b, -1), (d + b, -1)))
        for group, integers in enumerate(groups):
            row_valuations = Counter()
            for n, sign in integers:
                largest_integer = max(largest_integer, n)
                factors = factor(n)
                individual_prime_support.update(factors)
                for p, exponent in factors.items():
                    row_valuations[p] += sign * exponent
            for p, exponent in row_valuations.items():
                if exponent:
                    prime_supports[group].add(p)
                    valuation_sums[group][p] += e * exponent

    residuals = [{str(p): value for p, value in sorted(total.items()) if value}
                 for total in valuation_sums]
    require(not any(residuals), "Product valuation identity failed: " + str(residuals))
    signed_sum = sum(e for _, e in rows)
    absolute_sum = sum(abs(e) for _, e in rows)
    require(signed_sum > 0, "Relation must be oriented with positive coefficient sum")
    max_digits = max(len(str(abs(e))) for _, e in rows)
    for key, calculated in (("sum_e", signed_sum), ("sum_abs_e", absolute_sum),
                            ("support_size", len(rows)),
                            ("max_abs_e_digits", max_digits)):
        if key in data:
            require(integer(data[key]) == calculated, "Incorrect metadata: " + key)
    common_divisor = 0
    for _, e in rows:
        common_divisor = gcd(common_divisor, abs(e))

    # Paper convention: signed count = side 2 minus side 1. Thus a positive
    # table entry is on side 2 and the balancing squares are on side 1.
    # Every starting variable is completed by its own chain. The chain tail is
    # also added to the opposite side, so tail dimensions are common.
    D = 3 * d
    initial_dimensions = [0, 0]
    tail_dimension_per_side = 0
    chain_lengths = Counter()
    all_exponents = set()
    for b, e in rows:
        for c, signed_count in ((3 * b, 2 * e), (b, -2 * e),
                                (d - b, 2 * e), (d + b, 2 * e)):
            steps = chain(D, c)
            count = abs(signed_count)
            initial_dimensions[1 if signed_count > 0 else 0] += count
            tail_dimension_per_side += count * (len(steps) - 1)
            chain_lengths[len(steps)] += 1
            all_exponents.update(a for _, a, _ in steps)
        require(D // gcd(D, 3 * b) == d, "First denominator check failed")
        require(all(D // gcd(D, c) == D for c in (b, d - b, d + b)),
                "Other denominator check failed")
    require(initial_dimensions[1] - initial_dimensions[0] == 4 * signed_sum,
            "Variable imbalance failed")
    square_counts = [4 * signed_sum, 0]
    balanced_dimensions = [initial_dimensions[j] + square_counts[j]
                           + tail_dimension_per_side for j in (0, 1)]
    require(balanced_dimensions[0] == balanced_dimensions[1],
            "Balancing dimensions failed")
    cube_count = 1 if balanced_dimensions[0] % 2 else 2
    s0 = balanced_dimensions[0] + cube_count
    require(s0 % 2 == 0, "Seed dimension must be even")
    final_dimension = 4 * (s0 + 2) + 6 + 2

    return {
        "verification_passed": True,
        "relation_file": path.name,
        "relation_file_sha256": hashlib.sha256(raw).hexdigest(),
        "method": "Independent exact integer arithmetic; trial division of all six raw integers per row; no matrix or producer imported.",
        "d": d,
        "d_power_of_three": power_of_three,
        "D": D,
        "support_size": len(rows),
        "sum_e": str(signed_sum),
        "sum_abs_e": str(absolute_sum),
        "coefficient_gcd": str(common_divisor),
        "max_abs_e_digits": max_digits,
        "positive_coefficients": sum(e > 0 for _, e in rows),
        "negative_coefficients": sum(e < 0 for _, e in rows),
        "raw_factorizations_performed": 6 * len(rows),
        "largest_raw_integer": largest_integer,
        "largest_prime_divisor": max(individual_prime_support),
        "first_product_nonzero_row_prime_count": len(prime_supports[0]),
        "second_product_nonzero_row_prime_count": len(prime_supports[1]),
        "first_product_residual_valuations": residuals[0],
        "second_product_residual_valuations": residuals[1],
        "product_conclusion": "Both products are positive rational numbers. Every prime valuation is zero, so unique factorization makes each product exactly 1.",
        "chain_checks": {
            "distinct_table_chains_checked": 4 * len(rows),
            "chain_length_histogram_unweighted": dict(sorted(chain_lengths.items())),
            "minimum_exponent": min(all_exponents),
            "maximum_exponent": max(all_exponents),
            "all_weighted_degrees_one": True,
            "all_ordinary_monomial_degrees_at_least_three": True,
            "all_required_denominators_correct": True,
        },
        "seed_construction": {
            "side_convention": "Signed count is side 2 minus side 1: positive counts on side 2, negative counts on side 1; balancing squares on side 1.",
            "initial_variable_counts": [str(n) for n in initial_dimensions],
            "common_tail_variable_count_per_side": str(tail_dimension_per_side),
            "balancing_square_counts": [str(n) for n in square_counts],
            "balanced_dimension_before_final_cubes": str(balanced_dimensions[0]),
            "common_final_cube_count": cube_count,
            "ambient_dimension_s0": str(s0),
            "ambient_dimension_formula": "s0=4*sum_abs_e+2*sum_e+common_tail_variable_count_per_side+2",
            "hessian_ranks": [str(n) for n in square_counts],
            "orders": [2, 3],
        },
        "final_construction": {
            "definition": "q_j=p_j+x^5+y^7; f_j is the sum of four disjoint copies of q_j, six cubes, one eleventh power, and one thirteenth power.",
            "ambient_dimension": str(final_dimension),
            "ambient_dimension_formula": "4*s0+16",
            "hessian_ranks": [str(16 * signed_sum), "0"],
            "orders": [2, 3],
        },
        "scope": "This report verifies the finite relation and arithmetic of the indicated polynomial construction; it does not certify the topological or lattice-theoretic parts of the proof.",
    }


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("relation", nargs="?", type=Path,
                        default=root / "support" / "explicit-relation.json")
    parser.add_argument("report", nargs="?", type=Path,
                        default=root / "support" / "explicit-relation-verification.json")
    args = parser.parse_args()
    result = verify(args.relation)
    args.report.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
