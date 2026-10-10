#!/usr/bin/env python3
"""Reconstruct the volume and constrained-moment certificates exactly.

Run from any directory with Python 3 and SymPy:
    python scripts/check_scalar_certificates.py
    python scripts/check_scalar_certificates.py --json notes/scalar-checks.json

All acceptance tests use rational arithmetic or polynomial identities. Floating
point values in the report are display-only. This script reconstructs the
polynomials from H and the sine minorant, then independently converts their
power coefficients to Bernstein coefficients. It does not read a cached verdict
or depend on any other certificate script.

The accompanying mathematical proof supplies the compactness, separation,
calculus, Jacobi comparison, and Sobolev arguments. These arithmetic checks
include the endpoints 0 and 2 and the collapsed feasible weight interval.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import sympy as sp


Q = sp.Rational
x, z, u, q, w, t, beta = sp.symbols("x z u q w t beta", real=True)
REPORT: dict[str, object] = {}
CHECKS = 0


def check(condition: object, name: str) -> None:
    global CHECKS
    if not bool(condition):
        raise AssertionError(name)
    CHECKS += 1


def identity(lhs: sp.Expr, rhs: sp.Expr, name: str) -> None:
    check(sp.cancel(sp.expand(lhs - rhs)) == 0, name)


def number(value: sp.Expr) -> dict[str, object]:
    return {"exact": str(value), "approximation": float(value)}


def bernstein_coefficients(
    expression: sp.Expr, left: sp.Rational, right: sp.Rational
) -> list[sp.Expr]:
    """Use the explicit power-to-Bernstein formula, then verify reconstruction."""
    poly = sp.Poly(expression, x)
    degree = poly.degree()
    power = [
        sp.expand(
            (right - left) ** j
            * sum(
                poly.nth(k) * sp.binomial(k, j) * left ** (k - j)
                for k in range(j, degree + 1)
            )
        )
        for j in range(degree + 1)
    ]
    coefficients = [
        sum(
            power[j] * sp.binomial(i, j) / sp.binomial(degree, j)
            for j in range(i + 1)
        )
        for i in range(degree + 1)
    ]
    reconstructed = sum(
        coefficients[i] * sp.binomial(degree, i) * x**i * (1 - x) ** (degree - i)
        for i in range(degree + 1)
    )
    identity(
        expression.subs(x, left + (right - left) * x),
        reconstructed,
        "Bernstein reconstruction",
    )
    return coefficients


def arctan_sum(argument: sp.Rational, terms: int) -> sp.Expr:
    return sum((-1) ** k * argument ** (2 * k + 1) / (2 * k + 1) for k in range(terms))


def volume_checks() -> None:
    # Machin's identity pi = 16 atan(1/5) - 4 atan(1/239), together with
    # alternating-series bounds. The tangent computation verifies the identity
    # once the elementary range 0 < 4 atan(1/5)-atan(1/239) < pi/2 is observed.
    tan_twice = 2 * Q(1, 5) / (1 - Q(1, 5) ** 2)
    tan_four = 2 * tan_twice / (1 - tan_twice**2)
    check((tan_four - Q(1, 239)) / (1 + tan_four * Q(1, 239)) == 1, "Machin tangent identity")
    pi_lower = 16 * arctan_sum(Q(1, 5), 12) - 4 * arctan_sum(Q(1, 239), 13)
    pi_upper = 16 * arctan_sum(Q(1, 5), 13) - 4 * arctan_sum(Q(1, 239), 12)
    a0, b0 = Q(157, 50), Q(22, 7)
    check(a0 < pi_lower < pi_upper < b0, "strict rational bounds for pi")
    check(b0**2 < 10, "time-variance weakening")
    sine = a0 * z - (b0 * z) ** 3 / 6 + (a0 * z) ** 5 / 120 - (b0 * z) ** 7 / 5040
    identity(
        sine,
        Q(157, 50) * z - Q(5324, 1029) * z**3
        + Q(95388992557, 37500000000) * z**5
        - Q(155897368, 259416045) * z**7,
        "printed sine coefficients",
    )
    check(a0 - b0**3 / 24 - b0**7 / 322560 > Q(9, 5), "nonnegativity of sine minorant")

    small_f = q**2 * (3 + 5 * q + 6 * q**2)
    small_beta = q / (1 - q)
    identity(
        small_beta**2 * (3 - small_beta) - small_f,
        q**5 * (6 - 13 * q + 6 * q**2) / (1 - q) ** 3,
        "comparison-function difference",
    )
    check(Q(25, 64) < Q(2, 3), "both comparison polynomial factors nonnegative")
    check(small_f.subs(q, Q(25, 64)) == Q(7511875, 8388608) < 1, "small-interval cap")
    check(
        (small_beta**2 * (3 - small_beta)).subs(q, Q(25, 64))
        == Q(57500, 59319) > Q(15, 16),
        "large-interval lower bound",
    )
    identity(sp.diff(beta**2 * (3 - beta), beta), 3 * beta * (2 - beta), "monotone uncapped first branch")
    # For beta >= 2 the other branch is beta^2 >= 4; the capped function
    # remains 1 after its first crossing. The first branch is increasing up to 2.
    integrals = []
    f_u = small_f.subs(q, u**2)
    for left, right, f_piece, sine_argument, degree, lower in [
        (Q(0), Q(1, 2), f_u, u, 31, Q(11869, 10**6)),
        (Q(1, 2), Q(5, 8), f_u, 1 - u, 31, Q(30175, 10**6)),
        (Q(5, 8), Q(1), Q(15, 16), 1 - u, 23, Q(39518, 10**6)),
    ]:
        polynomial = sp.Poly(Q(9, 48) * a0 * f_piece * (1 - u**2 / 2) * sine.subs(z, sine_argument) ** 3, u)
        check(polynomial.degree() == degree, "volume polynomial degree")
        integral = sum(
            polynomial.nth(j) * (right ** (j + 1) - left ** (j + 1)) / (j + 1)
            for j in range(degree + 1)
        )
        check(integral > lower, "strict rational integral bound")
        integrals.append({"interval": [str(left), str(right)], "degree": degree, **number(integral), "printed_lower_bound": str(lower)})
    total = sum(Q(row["exact"]) for row in integrals)
    check(Q(11869 + 30175 + 39518, 10**6) > Q(163, 2000) > Q(2, 25) > Q(3, 40), "volume-deficit margin")
    REPORT["volume"] = {"integrals": integrals, "sum": number(total), "margin_over_3_40": number(total - Q(3, 40))}


def moment_checks() -> None:
    factor = 1 + z**2 / 40 - z**4 / 1152
    H = sp.sqrt(z) * factor
    Phi = sp.expand(16 * z * factor**2 + 9 * z * (1 - z))

    # The initial lower bound d >= 11/20 follows without any assumption
    # excluding z=0 or z=2. Delta is nonnegative throughout that closed interval.
    delta, c = z**2 * (4 - z**2) / 1152, Q(31, 1440)
    identity(factor, 1 + c * z**2 + delta, "lower bound for H factor")
    lower_phi = 25 * z - 9 * z**2 + Q(31, 45) * z**3
    identity(Phi - lower_phi, 16 * z * (2 * delta + (c * z**2 + delta) ** 2), "nonnegative Phi remainder")
    quadratic = 25 + Q(31, 45) * z**2 - Q(346, 25) * z
    identity(lower_phi - 16 * Q(11, 20) ** 2 * z**2, z * quadratic, "initial d bound polynomial")
    check(sp.diff(quadratic, z).subs(z, 2) < 0, "quadratic is decreasing on [0,2]")
    check(quadratic.subs(z, 2) == Q(17, 225) > 0, "quadratic endpoint margin")
    check(Q(9, 32) * 80 - 25 == -Q(5, 2), "strictly feasible first constraint")
    check(1 - Q(9, 32) * 4 == -Q(1, 8), "strictly feasible second constraint")

    L = Q(3, 8) + Q(3, 64) * z**2 - Q(35, 1024) * z**4
    V = Q(24, 5) - Q(16, 15) * z**2 - Q(7, 48) * z**4 + Q(7, 1152) * z**6
    check(sp.simplify(sp.diff(H, z, 3) - L * z ** Q(-5, 2)) == 0, "third derivative of H")
    identity(sp.diff(Phi, z, 3), V, "third derivative of Phi")
    check(32 * Q(11, 20) == Q(88, 5), "d coefficient")
    check(32 < Q(17, 3) ** 2, "4 sqrt(2) < 17/3")
    Lx, Vx = L.subs(z, 2 * x**2), V.subs(z, 2 * x**2)
    identity(Lx, Q(3, 8) + Q(3, 16) * x**4 - Q(35, 64) * x**8, "printed L input")
    identity(Vx, Q(24, 5) - Q(64, 15) * x**4 - Q(7, 3) * x**8 + Q(7, 18) * x**12, "printed V input")
    check(sp.degree(Lx, x) == 8, "L degree")
    minimum_L = min(bernstein_coefficients(Lx, Q(0), Q(1)))
    check(minimum_L == Q(1, 64) > Q(1, 100), "L exact coefficient minimum")
    D = Q(88, 5) * Lx - Q(17, 3) * x**5 * Vx
    check(sp.degree(D, x) == 17, "D degree")
    minima_D = [min(bernstein_coefficients(D, Q(j, 4), Q(j + 1, 4))) for j in range(4)]
    check(min(minima_D) == Q(2459668689, 5793382400) > Q(2, 5), "D exact coefficient minimum")

    Am, Bm = 1 - w**2, 4 - w**2
    Ap, Bp = 25 - 28 * w - 6 * w**2, 80 - 28 * w - 6 * w**2
    identity(Ap * Bm - Am * Bp, (2 - w) * (10 - 37 * w), "nonempty weight interval")
    check((Am / Bm).subs(w, Q(10, 37)) == (Ap / Bp).subs(w, Q(10, 37)), "collapsed weight interval endpoint")
    check(Q(5, 37) < Q(37, 100) ** 2, "sqrt(w/2) <= 37/100")
    R = 1 + x**4 / 10 - x**8 / 72
    Hw, H2 = sp.sqrt(2) * x * R, sp.sqrt(2) * R.subs(x, 1)
    wx = 2 * x**2
    Phi_w = 16 * Hw**2 + 9 * wx * (1 - wx)
    Phi_2 = 16 * H2**2 - 18
    J = 16 * ((1 - t) * Hw + t * H2) ** 2 - (1 - t) * Phi_w - t * Phi_2
    identity(J, -16 * t * (1 - t) * (H2 - Hw) ** 2 + 9 * ((1 - t) * (wx**2 - wx) + 2 * t), "J equals endpoint inequality")
    identity(sp.diff(J, t, 2), 32 * (H2 - Hw) ** 2, "convexity in endpoint weight")
    endpoint_data = []
    expected = [
        Q(58454914732902747377800095783827783501884053, 50000000000000000000000000000000000000000000),
        Q(132428032291164570287168821949356607977047, 770000000000000000000000000000000000000),
    ]
    for name, A, B, expected_minimum in zip(["minus", "plus"], [Am, Ap], [Bm, Bp], expected):
        A, B = A.subs(w, wx), B.subs(w, wx)
        P = sp.expand(32 * A * (B - A) * (R.subs(x, 1) - x * R) ** 2 - 9 * ((B - A) * (wx**2 - wx) + 2 * A) * B)
        identity(-B**2 * J.subs(t, A / B), P, "P is negative cleared endpoint J")
        check(sp.degree(P, x) == 22, "endpoint polynomial degree")
        minimum = min(bernstein_coefficients(P, Q(0), Q(37, 100)))
        check(minimum == expected_minimum > 1, "endpoint exact coefficient minimum")
        check(P.subs(x, 0) > 0 and P.subs(x, Q(37, 100)) > 0, "closed certificate endpoints")
        endpoint_data.append({"name": name, "degree": 22, "minimum": number(minimum)})

    # The derivative estimate in the variance argument is also valid at b=0,2.
    identity((1 + q / 2 - q**2 / 8) ** 2 - (1 + q), q**3 * (q - 8) / 64, "Sobolev chain-rule coefficient bound")
    # Here q=b^2/4 lies in [0,1], so the right side is nonpositive and
    # 1+q/2-q^2/8 >= 1, proving both sides of the claimed derivative bound.
    possibilities = [
        (chi, tau)
        for chi in range(2, 7)
        for tau in range(-chi + 2, chi - 1, 2)
        if tau != 0 and Q(abs(tau), chi) < Q(4, 15)
    ]
    check(possibilities == [(5, -1), (5, 1)], "integer obstruction")
    REPORT["moments"] = {
        "L_minimum": number(minimum_L),
        "D_subinterval_minima": [number(value) for value in minima_D],
        "endpoint_polynomials": endpoint_data,
        "integer_possibilities": possibilities,
        "closed_interval": "[0,2]; Bernstein domains closed; w=10/37 included",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="write the exact report to this path")
    args = parser.parse_args()
    volume_checks()
    moment_checks()
    REPORT["status"] = "PASS"
    REPORT["exact_checks"] = CHECKS
    REPORT["sympy_version"] = sp.__version__
    output = json.dumps(REPORT, indent=2) + "\n"
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
