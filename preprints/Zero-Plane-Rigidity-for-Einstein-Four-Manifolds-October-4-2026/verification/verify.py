#!/usr/bin/env python3
"""Reproduce the manuscript's finite exact arithmetic certificates offline.

Author: OpenAI. Run: python -B verify.py --check
All arithmetic decisions use fractions.Fraction. This is not a proof assistant.
"""
import sys
sys.dont_write_bytecode = True
import argparse
from fractions import Fraction as Q
import json
from math import comb
from pathlib import Path

from polynomial import Poly, interval_coefficients, rational, require, ring, triangle_coefficients

ROOT = Path(__file__).resolve().parent
RESULTS_FILE = ROOT / "results.json"
RESULTS = {
    "format_version": 1,
    "author": "OpenAI",
    "scope": "Finite polynomial identities, Bernstein coefficient certificates, and rational volume margins",
    "arithmetic": "Python standard library fractions.Fraction; no floating-point decisions",
    "identities": [],
    "interval_certificates": [],
    "triangle_certificates": [],
    "exact_values": {},
}


def identity(key, difference):
    require(difference == 0, "Identity failed: " + key)
    RESULTS["identities"].append({"key": key, "passed": True})


def scalar_claim(key, condition, detail):
    require(condition, "Exact assertion failed: " + key)
    RESULTS["exact_values"][key] = {"passed": True, **detail}


def interval(key, poly, intervals, floor, degree=None, strict=False, supplementary=False):
    degree = poly.degree() if degree is None else degree
    floor = rational(floor)
    record = {"key": key, "polynomial": poly.data(), "bernstein_degree": degree,
              "coefficient_floor": str(floor), "strict": strict,
              "supplementary": supplementary, "intervals": []}
    for left, right in intervals:
        coeffs = interval_coefficients(poly, left, right, degree)
        require(all(c > floor if strict else c >= floor for c in coeffs),
                "Coefficient bound failed: " + key)
        minimum = min(coeffs)
        record["intervals"].append({
            "left": str(rational(left)), "right": str(rational(right)),
            "coefficients": [str(c) for c in coeffs], "minimum": str(minimum),
            "minimizing_indices": [i for i, c in enumerate(coeffs) if c == minimum],
            "zero_indices": [i for i, c in enumerate(coeffs) if c == 0], "passed": True})
    record["passed"] = True
    RESULTS["interval_certificates"].append(record)
    return record


VERTICES = {
    "O": (0, 0), "S": (1, 0), "C": (1, 1), "U": (2, 0), "W0": (0, 2),
    "A": (Q(1, 2), Q(1, 2)), "B": (Q(3, 2), Q(1, 2)), "E": (1, Q(1, 2)),
}


def triangle(key, entries, names, degree, floor, determinant_floor=None, zeros=()):
    vertices = [VERTICES[name] for name in names]
    coefficients = [triangle_coefficients(p, vertices, degree) for p in entries]
    expected_zeros = set(zeros)
    actual_zeros = {ij for ij in coefficients[0]
                    if all(row[ij] == 0 for row in coefficients)}
    require(actual_zeros == expected_zeros, "Exact zero pattern failed: " + key)
    floor = rational(floor)
    determinant_floor = None if determinant_floor is None else rational(determinant_floor)
    output = []
    diagonal_minima, determinants = [], []
    for ij in coefficients[0]:
        values = [row[ij] for row in coefficients]
        record = {"index": [ij[0], ij[1], degree - sum(ij)],
                  "entries": [str(value) for value in values],
                  "zero": ij in actual_zeros}
        if ij not in actual_zeros:
            if len(values) == 1:
                require(values[0] >= floor, "Scalar triangle bound failed: " + key)
                diagonal_minima.append(values[0])
            else:
                r, h, off = values
                determinant = r * h - off * off
                require(min(r, h) >= floor, "Matrix diagonal bound failed: " + key)
                require(determinant >= determinant_floor, "Matrix determinant bound failed: " + key)
                diagonal_minima.extend([r, h])
                determinants.append(determinant)
                record["determinant"] = str(determinant)
        output.append(record)
    RESULTS["triangle_certificates"].append({
        "key": key, "vertices": list(names),
        "coordinates": [[str(rational(x)), str(rational(y))] for x, y in vertices],
        "bernstein_degree": degree, "polynomials": [p.data() for p in entries],
        "entry_order": ["scalar"] if len(entries) == 1 else ["11", "22", "12"],
        "coefficient_floor": str(floor),
        "determinant_floor": None if determinant_floor is None else str(determinant_floor),
        "zero_indices": [list(ij) for ij in sorted(actual_zeros)],
        "minimum_diagonal_or_scalar": str(min(diagonal_minima)),
        "minimum_determinant": str(min(determinants)) if determinants else None,
        "coefficients": output, "passed": True})
    return coefficients


def swap(poly):
    values = list(ring(*poly.variables))
    vi, bi = poly.variables.index("v"), poly.variables.index("b")
    values[vi], values[bi] = values[bi], values[vi]
    return poly.substitute(values)


def definitions(v, b):
    D, h = Q(158), Q(17, 10)
    a, s, delta = v - 1, b - 1, 2 - v - b
    n, t = delta / 2, (v - b) / 2
    z = [Q(k, 4) for k in (-43, -45, -63, 21, 183, 208, 61, 46, 101, 79, -41)]
    kappa = (-D * (a - s) / 6 + z[0] * a ** 2 + (60 - 2 * D / 9 + 2 * z[0]) * a * s
             + z[1] * s ** 2 + sum(z[2 + i] * a ** i * s ** (3 - i) for i in range(4))
             + sum(z[6 + i] * a ** i * s ** (4 - i) for i in range(5)))
    kappab = swap(kappa)
    M = 1 - Q(3, 8) * (v - b)
    m, c, K = M ** 2, Q(2, 5) - Q(3, 10) * v * b, 4 + v ** 2 + b ** 2
    theta = (n ** 2 * (1 - n) * (105 + 5 * n)
             + t ** 2 * (4 + 360 * n - 586 * n ** 2) - 4 * t ** 4) / 4
    Pk, Pl = 300 * m + 160 * h * delta, 35 * m * v
    P0 = Pk + 30 * h * v
    Xv = m * (-70 + 100 * v - 25 * v ** 2 - 5 * b ** 2) + Q(5, 3) * h * (6 * (a ** 2 + s ** 2) + 32 * a * delta)
    rv, rb = 1 + 6 * v + v ** 2, 1 + 6 * b + b ** 2
    alpha = Q(5, 4)
    Sstar = 4 * (alpha + 1 / alpha) * v * b + (alpha * b * (1 - v) ** 2 + v * (1 - b) ** 2 / alpha) / 2
    KJ = K * (kappa.derivative("b") + kappab.derivative("v")) / 2 - D
    Hv = 8 * v * K * theta * (1 + v) - rv * (v * D + K * (v * (Xv + kappa.derivative("v")) + 2 * kappa / 3))
    E0 = D * (1 - delta ** 2 / 4) * (v - b) ** 2 + 30 * h * delta * (v ** 2 * a ** 2 + b ** 2 * s ** 2) + 6 * (a * v * kappa + s * b * kappab)
    F, Lv, Lb = c * E0 - theta ** 2, 10 * h * delta * v - kappa, 10 * h * delta * b - kappab
    return locals()


def matrix_A(v, b, sigma):
    f = definitions(v, b)
    m, h, d, kap = f["m"], f["h"], f["delta"], f["kappa"]
    P0, Pk, Pl = f["P0"], f["Pk"], f["Pl"]
    lam = 6 * (sigma * v ** 2 + b ** 2 - v - b) - 26 * d
    K2 = m * (42 + 3 * b ** 2 + 10 * v ** 2) - h * lam
    K1 = 5 * K2 + m * (300 * v * sigma + 140 * v ** 2) + 160 * h * d * v * sigma
    K12 = m * (75 * v + 35 * v ** 2 * sigma) + 40 * h * d * v
    return (P0 * (v * K1 - 5 * kap) - (1 + sigma) * v ** 2 * Pk ** 2,
            P0 * (v * K2 - kap) - (1 + sigma) * v ** 2 * Pl ** 2,
            P0 * v * K12 - (1 + sigma) * v ** 2 * Pk * Pl)


def check_engine():
    x, y = ring("x", "y")
    identity("engine.binomial_product", (x + y) ** 2 - x ** 2 - 2 * x * y - y ** 2)
    identity("engine.derivative", ((x + y) ** 3).derivative("x") - 3 * (x + y) ** 2)
    identity("engine.exact_division", ((x ** 3 - y ** 3).divide_exact(x - y)) - (x ** 2 + x * y + y ** 2))
    (u,) = ring("u")
    require(interval_coefficients(u ** 2, 0, 1, 2) == [Q(0), Q(0), Q(1)], "Engine univariate normalization")
    tri = triangle_coefficients(x * y, [(1, 0), (0, 1), (0, 0)], 2)
    require(tri[1, 1] == Q(1, 2) and sum(tri.values()) == Q(1, 2), "Engine triangle normalization")
    require((u ** 2).integral(0, 1) == Q(1, 3), "Engine integration")
    scalar_claim("engine.normalizations", True, {"passed_examples": 3})


def check_scalar_certificates():
    (b,) = ring("b")
    Rb = 1 + b ** 2 / 40 - b ** 4 / 1152
    Hterms = [(Q(1, 2), Q(1)), (Q(5, 2), Q(1, 40)), (Q(9, 2), -Q(1, 1152))]
    Hthird_scaled = sum(co * ex * (ex - 1) * (ex - 2) * b ** int(ex - Q(1, 2)) for ex, co in Hterms)
    Hratio = sum(2 * ex * co * b ** int(ex - Q(1, 2)) for ex, co in Hterms)
    L9 = Q(3, 8) + Q(3, 64) * b ** 2 - Q(35, 1024) * b ** 4
    V9 = Q(24, 5) - Q(16, 15) * b ** 2 - Q(7, 48) * b ** 4 + Q(7, 1152) * b ** 6
    Phi = 16 * b * Rb ** 2 + 9 * b * (1 - b)
    identity("eq9.H_third_derivative", Hthird_scaled - L9)
    identity("eq9.Phi_third_derivative", Phi.derivative("b", 3) - V9)
    identity("eq9.H_derivative_ratio", Hratio - (1 + b ** 2 / 8 - b ** 4 / 128))
    identity("eq9.R_lower_remainder", Rb - (1 + Q(31, 1440) * b ** 2) - b ** 2 * (4 - b ** 2) / 1152)
    q = 16 * (1 + Q(62, 1440) * b ** 2) + 9 - (9 + 16 * Q(11, 20) ** 2) * b
    identity("eq9.printed_moment_quadratic", q - (25 + Q(31, 45) * b ** 2 - Q(346, 25) * b))
    scalar_claim("eq9.moment_lower_bound", q.derivative("b", 2).evaluate([0]) > 0 and q.derivative("b").evaluate([2]) < 0 and q.evaluate([2]) == Q(17, 225),
                 {"q_at_2": str(q.evaluate([2])), "q_prime_at_2": str(q.derivative("b").evaluate([2])), "q_second": str(q.derivative("b", 2).evaluate([0]))})
    mass = Q(9, 32)
    scalar_claim("eq9.printed_strictly_feasible_measure", 80 * mass - 25 == -Q(5, 2)
                 and 1 - 4 * mass == -Q(1, 8),
                 {"mass_at_2": str(mass), "first_constraint": "-5/2", "second_constraint": "-1/8"})
    identity("eq9.weight_interval_nonempty", (25 - 28 * b - 6 * b ** 2) * (4 - b ** 2)
             - (1 - b ** 2) * (80 - 28 * b - 6 * b ** 2) - (2 - b) * (10 - 37 * b))
    X, P = ring("X", "P")
    identity("eq9.moment_ratio_clearing", 15 * (Q(2, 3) * (X - P) - Q(1, 5) * (1 + X + P))
             - (7 * X - 13 * P - 3))
    (x,) = ring("x")
    Lx, Vx = L9.substitute([2 * x ** 2]), V9.substitute([2 * x ** 2])
    identity("eq9.printed_L_input", Lx - (Q(3, 8) + Q(3, 16) * x ** 4 - Q(35, 64) * x ** 8))
    identity("eq9.printed_V_input", Vx - (Q(24, 5) - Q(64, 15) * x ** 4 - Q(7, 3) * x ** 8 + Q(7, 18) * x ** 12))
    quarters = [(Q(i, 4), Q(i + 1, 4)) for i in range(4)]
    L_record = interval("eq9.L", Lx, [(0, 1)], Q(1, 100), 8)
    D_record = interval("eq9.third_derivative_sign", Q(88, 5) * Lx - Q(17, 3) * x ** 5 * Vx, quarters, Q(2, 5), 17)
    for name, record, expected in [("L", L_record, Q(1, 64)),
                                   ("D_star", D_record, Q(2459668689, 5793382400))]:
        least = min(Q(part["minimum"]) for part in record["intervals"])
        scalar_claim("eq9.printed_minimum." + name, least == expected,
                     {"exact_minimum": str(least), "printed_minimum": str(expected)})
    R = 1 + x ** 4 / 10 - x ** 8 / 72
    w = 2 * x ** 2
    for name, A, B in [("lower", 1 - w ** 2, 4 - w ** 2),
                       ("upper", 25 - 28 * w - 6 * w ** 2, 80 - 28 * w - 6 * w ** 2)]:
        gap = R.evaluate([1]) - x * R
        p = 32 * A * (B - A) * gap ** 2 - 9 * ((B - A) * (w ** 2 - w) + 2 * A) * B
        # This second form is the numerator obtained by multiplying the rational expression by B^2.
        numerator = 32 * (A * B - A ** 2) * gap ** 2 - 9 * ((B ** 2 - A * B) * (w ** 2 - w) + 2 * A * B)
        identity("eq9.endpoint_clearing." + name, numerator - p)
        endpoint_record = interval("eq9.endpoint." + name, p, [(0, Q(37, 100))], 1, 22)
        expected = {
            "lower": Q(58454914732902747377800095783827783501884053,
                       50000000000000000000000000000000000000000000),
            "upper": Q(132428032291164570287168821949356607977047,
                       770000000000000000000000000000000000000),
        }[name]
        least = Q(endpoint_record["intervals"][0]["minimum"])
        scalar_claim("eq9.printed_minimum.endpoint_" + name, least == expected,
                     {"exact_minimum": str(least), "printed_minimum": str(expected)})
        interval("eq9.endpoint_denominator." + name, B, [(0, Q(37, 100))], 0, strict=True, supplementary=True)
    scalar_claim("eq9.endpoint_range_and_radical", Q(5, 37) < Q(37, 100) ** 2 and Q(17, 3) ** 2 > 32,
                 {"endpoint_upper_square": str(Q(37, 100) ** 2), "required_square": str(Q(5, 37)), "comparison_square": str(Q(17, 3) ** 2)})
    (v,) = ring("v")
    h = Q(17, 10)
    A0 = Q(27, 320) * v * (Q(15, 2) + Q(2, 3) * v)
    L0 = Q(9, 20) * v * (Q(7, 4) - Q(3, 4) * v)
    C0 = Q(7, 5) * h - A0 - L0
    det = 4 * C0 * ((h - A0) * (2 - v) + Q(2, 5) * h * v) - (2 - v) * (2 * A0 + L0) ** 2
    for name, poly, degree, expected in [
            ("C0", C0, 2, [Q(3971, 3200), Q(1063, 1600)]),
            ("determinant", det, 5, [Q(101027, 20000), Q(283729, 400000)])]:
        record = interval("eq19.defect_" + name, poly, [(0, 1), (1, 2)], Q(1, 2), degree, strict=True)
        minima = [Q(part["minimum"]) for part in record["intervals"]]
        scalar_claim("eq19.printed_minima." + name, minima == expected,
                     {"exact_minima": [str(c) for c in minima], "printed_minima": [str(c) for c in expected]})
    (r,) = ring("r")
    sigma = (3 * r - r ** 3) / 2
    identity("eq20.one_minus_sigma", 1 - sigma - (r - 1) ** 2 * (r + 2) / 2)
    identity("eq20.one_plus_sigma", 1 + sigma - (2 - r) * (r + 1) ** 2 / 2)
    auxiliary = 4 * r * (r + 3) - (r - 1) * (r + 2) * (r + 1) ** 2
    interval("eq20.g_majorant_auxiliary", auxiliary, [(1, 2)], 4, 4, supplementary=True)
    (u,) = ring("u")
    omega, mu = Q(27, 128), Q(9, 32)
    A = Q(67, 50) * (1 + u ** 2)
    G = Q(27, 100) * (1 + u ** 2) * u ** 2 + 3 * omega * (1 + u) ** 2 + mu * (1 + u) * (1 - u ** 3)
    H = Q(27, 100) * (1 + u ** 2) + omega * (17 + 19 * u ** 2) * (1 + u) ** 2 / 12 - mu * (1 + u) * (1 - u ** 3)
    L = omega * (1 + u) ** 2 * (Q(19, 3) + Q(7, 2) * u ** 2) + Q(3, 4) * (1 + u) * (1 + u ** 3)
    Z = L ** 2 - 4 * A * (G + u ** 2 * H)
    interval("eq20.G", G, [(0, 1)], Q(9, 10), 4)
    interval("eq20.H", H, [(0, 1)], Q(1, 4), 4)
    interval("eq20.minus_Z", -Z, [(0, Q(1, 16))], Q(13, 100), 8)
    interval("eq20.radical", 64 * A ** 2 * u ** 2 * G * H - Z ** 2, [(Q(1, 16), 1)], Q(3, 25), 16)
    v, b, ur = ring("v", "b", "u")
    lift = lambda poly: poly.substitute([ur])
    gv, gb = Q(19, 3) - 3 * v - Q(17, 12) * b, Q(7, 2) - Q(19, 12) * b
    M, Mb = 1 - Q(3, 8) * (v - b), 1 - Q(3, 8) * (b - v)
    direct_num = ((Q(67, 50) + Q(27, 100) * v * b) * (1 + ur ** 2) * (b + v * ur ** 2)
                  - v * b * (omega * (1 + ur) ** 2 * (gv + gb * ur ** 2) + Q(3, 4) * (1 + ur) * (M + Mb * ur ** 3)))
    claimed_num = lift(A) * b + lift(A) * ur ** 2 * v + v * b * (lift(G) * v + lift(H) * b - lift(L))
    identity("eq20.enlarged_difference_cleared", direct_num - claimed_num)
    identity("eq20.quartic_coefficient", Q(10, 9) * (h - Q(67, 50) - Q(27, 100) * v * b) - (Q(2, 5) - Q(3, 10) * v * b))


def check_matrix_identities():
    # Congruence by diag(sqrt(3),1,1) removes all irrational entries.
    # This is the coordinate change p=sqrt(3) P; its norm matrix is diag(5,5,1).
    v, b, sigma, rho = ring("v", "b", "sigma", "rho")
    zero = 0 * v
    B = [[4 * v * sigma, -4 * v * rho, zero],
         [-4 * v * rho, -4 * v * sigma, -v], [zero, -v, zero]]
    CN = [[4 * v ** 2, zero, -rho * v ** 2],
          [zero, -4 * v ** 2, -sigma * v ** 2], [-rho * v ** 2, -sigma * v ** 2, zero]]
    metric, inverse = [Q(5), Q(5), Q(1)], [Q(1, 5), Q(1, 5), Q(1)]
    EB = [[sum(B[i][k] * inverse[k] * B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
    EB_expected = [[Q(16, 5) * v ** 2, zero, Q(4, 5) * rho * v ** 2],
                   [zero, Q(21, 5) * v ** 2, Q(4, 5) * sigma * v ** 2],
                   [Q(4, 5) * rho * v ** 2, Q(4, 5) * sigma * v ** 2, v ** 2 / 5]]
    G_expected = [
        [-210 - 15 * b ** 2 + 300 * sigma * v - 75 * v ** 2, -300 * rho * v, -35 * rho * v ** 2],
        [-300 * rho * v, -210 - 15 * b ** 2 - 300 * sigma * v - 190 * v ** 2, -75 * v - 35 * sigma * v ** 2],
        [-35 * rho * v ** 2, -75 * v - 35 * sigma * v ** 2, -42 - 3 * b ** 2 - 10 * v ** 2],
    ]
    for i in range(3):
        for j in range(i, 3):
            identity(f"eq12.inverse_metric_square_scaled.{i}{j}", (EB[i][j] - EB_expected[i][j]).reduce_circle())
            G = 75 * B[i][j] + Q(25, 3) * CN[i][j] - Q(100, 3) * EB[i][j]
            if i == j:
                G += (-42 - 3 * b ** 2 - Q(10, 3) * v ** 2) * metric[i]
            if i == j == 0:
                G += 15 * v ** 2
            identity(f"eq12.full_matrix_scaled.{i}{j}", (G - G_expected[i][j]).reduce_circle())
    f = definitions(v, b)
    h, m, d, P0, Pk, Pl = [f[key] for key in ("h", "m", "delta", "P0", "Pk", "Pl")]
    X = m * G_expected[0][0] / 3 + Q(5, 3) * h * (6 * (sigma * v ** 2 + b ** 2 - v - b) - 26 * d) + 40 * h * d * B[0][0] / 3
    Xaxial = X.substitute([v, b, 1, rho])
    identity("eq21.axial_Xv", Xaxial - f["Xv"])
    identity("eq21.pp_loss", Xaxial - X - (1 - sigma) * v * P0 / 3)
    identity("eq21.pk_cross_scaled", m * G_expected[0][1] + 40 * h * d * B[0][1] + v * rho * Pk)
    identity("eq21.pl_cross_scaled", m * G_expected[0][2] + 40 * h * d * B[0][2] + v * rho * Pl)
    identity("eq21.P0_relation", P0 - Pk - 30 * h * v)
    A_sigma = matrix_A(v, b, sigma)
    target = (v ** 2 * (30 * h * v) ** 2,
              v ** 2 * (Pl ** 2 + 6 * h * v * P0),
              -v ** 2 * 30 * h * v * Pl)
    for index, (entry, expected) in enumerate(zip(A_sigma, target)):
        identity(f"eq21.sigma_monotonicity.{index}", -entry.derivative("sigma") - expected)
    v, b = ring("v", "b")
    f = definitions(v, b)
    K, rv, rb, theta, kap, Xv, D = [f[key] for key in ("K", "rv", "rb", "theta", "kappa", "Xv", "D")]
    cleared = 8 * v * K * theta * (1 + v) - v * K * rv * Xv - v * D * rv - v * K * rv * kap.derivative("v") - Q(2, 3) * K * rv * kap
    identity("eq22.diagonal_clearing.v", cleared - f["Hv"])
    identity("eq22.diagonal_clearing.b", swap(cleared) - swap(f["Hv"]))
    alpha, star = f["alpha"], f["Sstar"]
    identity("eq22.Sstar_AMGM_pair", 2 * star - alpha * b * rv - v * rb / alpha)
    identity("eq22.Sstar_square_majorant", star ** 2 - v * b * rv * rb - (alpha * b * rv - v * rb / alpha) ** 2 / 4)
    v, b, sigma, sigmab = ring("v", "b", "sigma", "sigmab")
    f = definitions(v, b)
    d, h, kap, kappab = f["delta"], f["h"], f["kappa"], f["kappab"]
    potential = (-30 * h * d * (v ** 2 * (1 - 2 * sigma * v + v ** 2) + b ** 2 * (1 - 2 * sigmab * b + b ** 2))
                 - f["D"] * (1 - d ** 2 / 4) * (v - b) ** 2
                 + 6 * kap * v * (1 - sigma * v) + 6 * kappab * b * (1 - sigmab * b))
    identity("eq23.potential_decomposition", potential + f["E0"] + 6 * v ** 2 * (1 - sigma) * f["Lv"] + 6 * b ** 2 * (1 - sigmab) * f["Lb"])
    (z,) = ring("z")
    identity("final.R_strictness", 1 + 6 * z ** 2 + z ** 4 - 4 * z * (1 + z ** 2) - (z - 1) ** 4)


def check_triangle_certificates():
    v, b = ring("v", "b")
    f = definitions(v, b)
    A = matrix_A(v, b, 1)
    B = (f["Hv"], swap(f["Hv"]), f["Sstar"] * f["KJ"])
    Fplus = f["F"] + 12 * f["c"] * f["delta"] ** 2 * f["Lb"]
    rows = [
        ("eq21.A.OSC", A, ("O", "S", "C"), 8, 16000, 53000000, set()),
        ("eq21.A.OCW0", A, ("O", "C", "W0"), 8, 890, 3900000, set()),
        ("eq21.A.SCU", A, ("S", "C", "U"), 8, 2400, 3500000, set()),
        ("eq22.B.OAS", B, ("O", "A", "S"), 9, 43, 1050, set()),
        ("eq22.B.ASE", B, ("A", "S", "E"), 9, 43, 490, set()),
        ("eq22.B.ACE", B, ("A", "C", "E"), 10, 2, 21, {(0, 10)}),
        ("eq22.B.SBE", B, ("S", "B", "E"), 9, 43, 1300, set()),
        ("eq22.B.CBE", B, ("C", "B", "E"), 10, Q(13, 100), 4, {(9, 1), (10, 0)}),
        ("eq22.B.SUB", B, ("S", "U", "B"), 9, 5, 290, set()),
        ("eq23.Lv.OCU", (f["Lv"],), ("O", "C", "U"), 6, Q(9, 10), None, {(0, 6)}),
        ("eq23.Fplus.OSC", (Fplus,), ("O", "S", "C"), 9, Q(19, 100), None,
         {(i, j) for i in range(3) for j in range(3 - i)}),
        ("eq23.Fplus.SCU", (Fplus,), ("S", "C", "U"), 9, Q(9, 1000), None,
         {(i, j) for i in range(10) for j in range(10 - i) if j >= 7} | {(0, 6)}),
    ]
    cbe = None
    for key, entries, vertices, degree, floor, det_floor, zeros in rows:
        coefficients = triangle(key, entries, vertices, degree, floor, det_floor, zeros)
        if key == "eq22.B.CBE":
            cbe = coefficients
    triples = {
        (8, 0): (Q(11041, 810), Q(4063, 810), Q(60557, 16200)),
        (8, 1): (Q(4328, 405), Q(839, 405), Q(3977, 2700)),
        (8, 2): (Q(191, 81), Q(191, 81), -Q(1189, 1350)),
    }
    for index, expected in triples.items():
        actual = tuple(row[index] for row in cbe)
        scalar_claim("eq22.printed_CBE." + ".".join(map(str, index)), actual == expected,
                     {"index": list(index), "triple_11_22_12": list(map(str, actual))})
    return f


def check_F_expansion(f):
    n, t = ring("n", "t")
    Fnt = f["F"].substitute([1 - n + t, 1 - n - t])
    (nn,) = ring("n")
    fj = [
        nn ** 3 * (1 - nn) * (53511 * nn ** 4 - 151593 * nn ** 3 + 222537 * nn ** 2 - 83607 * nn + 10256) / 240,
        nn * (19389 * nn ** 5 - 418926 * nn ** 4 + 523719 * nn ** 3 - 289776 * nn ** 2 + 67782 * nn + 10564) / 60,
        (-1260129 * nn ** 4 + 1370598 * nn ** 3 - 451164 * nn ** 2 + 23442 * nn + 74) / 60,
        (-12200 * nn ** 2 + 2601 * nn + 75) / 10,
        0 * nn - Q(23, 5),
    ]
    identity("eq23.F_full_even_expansion", Fnt - sum(p.substitute([n]) * t ** (2 * j) for j, p in enumerate(fj)))
    # Full equality rules out ALL unlisted powers, including odd powers and powers above eight.
    require(Fnt.degree("t") == 8, "Unexpected F degree in t")
    divisors = [nn ** 3 * (1 - nn), nn * (1 - nn), 1 - nn, 1 - nn, 1 - nn]
    degrees, floors = [4, 6, 7, 7, 7], [3, 31, Q(1, 5), Q(12, 5), Q(9, 5)]
    quarters = [(Q(i, 4), Q(i + 1, 4)) for i in range(4)]
    for i in range(5):
        numerator = sum(Q(comb(i, j), comb(4, j)) * fj[j] * (1 - nn) ** (2 * j) for j in range(i + 1))
        quotient = numerator.divide_exact(divisors[i])
        identity(f"eq23.F_factor_divisibility.{i}", quotient * divisors[i] - numerator)
        interval(f"eq23.F_quarters.{i}", quotient, quarters, floors[i], degrees[i])


def check_volume_and_supplementary_bounds():
    (z,) = ring("z")
    a0, b0 = Q(157, 50), Q(22, 7)
    sine = a0 * z - (b0 * z) ** 3 / 6 + (a0 * z) ** 5 / 120 - (b0 * z) ** 7 / 5040
    identity("volume.printed_sine_polynomial", sine - (Q(157, 50) * z - Q(5324, 1029) * z ** 3
             + Q(95388992557, 37500000000) * z ** 5 - Q(155897368, 259416045) * z ** 7))
    elementary_sine_floor = a0 - b0 ** 3 / 24 - b0 ** 7 / 322560
    scalar_claim("volume.printed_sine_positive_floor", elementary_sine_floor > Q(9, 5),
                 {"exact_floor": str(elementary_sine_floor), "strict_lower_bound": "9/5"})
    quotient = sine.divide_exact(z)
    interval("volume.S_over_z_positive", quotient, [(0, Q(1, 2))], 0, 6, strict=True, supplementary=True)
    (u,) = ring("u")
    f = u ** 4 * (3 + 5 * u ** 2 + 6 * u ** 4)
    factor = 6 - 13 * u ** 2 + 6 * u ** 4
    identity("volume.f_comparison_numerator", u ** 4 * (3 - 4 * u ** 2) - f * (1 - u ** 2) ** 3 - u ** 10 * factor)
    interval("volume.f_comparison_factor", factor, [(0, Q(5, 8))], 0, 4, strict=True, supplementary=True)
    beta = Q(25, 39)
    scalar_claim("volume.cutoff_comparisons", f.evaluate([Q(5, 8)]) <= 1
                 and beta ** 2 * (3 - beta) == Q(57500, 59319) > Q(15, 16),
                 {"f_at_cutoff": str(f.evaluate([Q(5, 8)])), "beta_squared_3_minus_beta": str(beta ** 2 * (3 - beta))})
    Sleft, Sright = sine.substitute([u]), sine.substitute([1 - u])
    lower_integrand = u ** 2 * (u ** 4 / 2 + u ** 6 / 3)
    pieces = [
        ("upper_1", Q(9, 48) * a0, f * (1 - u ** 2 / 2) * Sleft ** 3,
         0, Q(1, 2), 31, Q(11869, 10 ** 6)),
        ("upper_2", Q(9, 48) * a0, f * (1 - u ** 2 / 2) * Sright ** 3,
         Q(1, 2), Q(5, 8), 31, Q(30175, 10 ** 6)),
        ("upper_3", Q(9, 48) * a0, Q(15, 16) * (1 - u ** 2 / 2) * Sright ** 3,
         Q(5, 8), 1, 23, Q(39518, 10 ** 6)),
        ("lower_1", a0 ** 3 / 27, lower_integrand * Sleft,
         0, Q(1, 2), 15, Q(698, 10 ** 6)),
        ("lower_2", a0 ** 3 / 27, lower_integrand * Sright,
         Q(1, 2), 1, 15, Q(40554, 10 ** 6)),
    ]
    values = {}
    for name, prefactor, poly, left, right, degree, floor in pieces:
        value = prefactor * poly.integral(left, right)
        scalar_claim("volume.printed_piece." + name, poly.degree() == degree and value > floor,
                     {"integrand": poly.data(), "prefactor": str(prefactor),
                      "left": str(rational(left)), "right": str(rational(right)),
                      "degree": degree, "exact_integral_with_prefactor": str(value),
                      "strict_lower_bound": str(floor)})
        values[name] = value
    upper_saved = sum(values[name] for name in ("upper_1", "upper_2", "upper_3"))
    lower_constant = Q(2, 9) * (a0 ** 2 - 4)
    scalar_claim("volume.printed_lower_constant", lower_constant == Q(4883, 3750),
                 {"exact_constant": str(lower_constant)})
    lower = lower_constant + values["lower_1"] + values["lower_2"]
    upper_floor_sum = sum(row[-1] for row in pieces[:3])
    lower_floor_sum = lower_constant + sum(row[-1] for row in pieces[3:])
    scalar_claim("volume.printed_piece_floor_sums", upper_floor_sum > Q(163, 2000) > Q(2, 25)
                 and lower_floor_sum > Q(1343, 1000) > Q(4, 3),
                 {"upper_floor_sum": str(upper_floor_sum), "upper_printed_bound": "163/2000",
                  "lower_floor_sum_with_constant": str(lower_floor_sum), "lower_printed_bound": "1343/1000"})
    expected_upper = Q(35568414570146708970215164653657279684840568049287583618357776852209994707811168145719343,
                       436079249052527988124474363762562231471002196310491136000000000000000000000000000000000000)
    expected_lower = Q(325513803292178267556854357335457, 242308366210310400000000000000000)
    scalar_claim("volume.upper_saved", upper_saved == expected_upper and upper_saved > Q(163, 2000) > Q(2, 25) > Q(3, 40),
                 {"exact_value": str(upper_saved), "asserted_bound": "163/2000", "required_bound": "3/40", "sine_power": 3})
    scalar_claim("volume.lower", lower == expected_lower and lower > Q(1343, 1000) > Q(67, 50) > Q(4, 3),
                 {"exact_value": str(lower), "asserted_bound": "1343/1000", "required_bound": "4/3", "sine_power": 1})
    (b,) = ring("b")
    ratio = 1 + b ** 2 / 8 - b ** 4 / 128
    identity("eq9.H_ratio_square_bound", 1 + b ** 2 / 4 - ratio ** 2 - b ** 6 * (32 - b ** 2) / 16384)
    interval("eq9.H_ratio_positive", ratio, [(0, 2)], 0, 4, strict=True, supplementary=True)


def compute():
    check_engine()
    check_scalar_certificates()
    check_matrix_identities()
    family = check_triangle_certificates()
    check_F_expansion(family)
    check_volume_and_supplementary_bounds()
    RESULTS["summary"] = {
        "identities": len(RESULTS["identities"]),
        "interval_certificate_rows": len(RESULTS["interval_certificates"]),
        "reported_interval_rows": sum(not r["supplementary"] for r in RESULTS["interval_certificates"]),
        "triangle_certificate_rows": len(RESULTS["triangle_certificates"]),
        "exact_value_assertions": len(RESULTS["exact_values"]),
        "all_passed": True,
    }
    return RESULTS


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--check", action="store_true", help="Recompute and compare to the bundled results (default)")
    modes.add_argument("--write", action="store_true", help="Recompute and replace results.json beside this script")
    args = parser.parse_args()
    result = compute()
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.write:
        temporary = ROOT / ".results.json.tmp"
        temporary.write_text(encoded, encoding="utf-8")
        temporary.replace(RESULTS_FILE)
    else:
        require(RESULTS_FILE.is_file(), "Bundled results.json is missing; run --write to create it")
        require(RESULTS_FILE.read_text(encoding="utf-8") == encoded,
                "Recomputed exact results differ from bundled results.json")
    print("PASS: all exact identities, coefficient bounds, zero patterns, and rational volume margins.")
    print(json.dumps(result["summary"], sort_keys=True))


if __name__ == "__main__":
    main()
