#!/usr/bin/env python3
"""Exact rational finite quadrature for S[{1,3,4},{1,3,4}].

All finite arithmetic uses fractions.Fraction. The analytic quadrature and
transcendental error proof gives abs(S_exact - S_finite) < 10^-12 per entry.
The N=64 certificate is independent of the full Arb finite certificate.
Its complete entry-error estimate is proved in the article appendix.
"""

from fractions import Fraction as F
from functools import lru_cache
import json
import time

from certificate_data import load_data, provenance, write_result


SCALE = 10**40
PI = F("3.141592653589793238462643383279502884")
BETA = F(".866025403784438646763723170752936183")
H = F(2, 5)
B = F(4, 3)
N = 64
J = [1, 3, 4]
ENTRY_ERROR = F(1, 10**12)


class C:
    """Complex numbers with exact rational real and imaginary components."""

    __slots__ = ("r", "i")

    def __init__(self, r=0, i=0):
        self.r = F(r)
        self.i = F(i)

    def __add__(self, other):
        other = to_c(other)
        return C(self.r + other.r, self.i + other.i)

    __radd__ = __add__

    def __neg__(self):
        return C(-self.r, -self.i)

    def __sub__(self, other):
        return self + -to_c(other)

    def __rsub__(self, other):
        return to_c(other) + -self

    def __mul__(self, other):
        if not isinstance(other, C):
            return C(self.r * other, self.i * other)
        return C(self.r * other.r - self.i * other.i,
                 self.r * other.i + self.i * other.r)

    __rmul__ = __mul__

    def __truediv__(self, other):
        if not isinstance(other, C):
            return C(self.r / other, self.i / other)
        denominator = other.r * other.r + other.i * other.i
        return C((self.r * other.r + self.i * other.i) / denominator,
                 (self.i * other.r - self.r * other.i) / denominator)

    def __rtruediv__(self, other):
        return to_c(other) / self


def to_c(value):
    return value if isinstance(value, C) else C(value)


def floor_rational(value):
    return F((value * SCALE).__floor__(), SCALE)


def floor_complex(value):
    return C(floor_rational(value.r), floor_rational(value.i))


I = C(0, 1)


def estar(u):
    x = I * PI * to_c(u) / 1024
    term = C(1)
    value = C(1)
    for q in range(1, 33):
        term = term * x / q
        value = value + term
    value = floor_complex(value)
    for _ in range(10):
        value = floor_complex(value * value)
    return value


@lru_cache(None)
def ereal(u):
    # The target exp(i*pi*u) is 2-periodic. The reduced rational evaluation
    # has direct error below 1e-32 and keeps rational inputs short.
    return estar(u % 2)


def atan_bracket(d):
    upper = sum((F((-1)**k, (2*k + 1) * d**(2*k + 1))
                 for k in range(29)), F(0))
    return upper - F(1, 59 * d**59), upper


def decimal_out(value, places=22, upper=False):
    scaled = value * 10**places
    integer = scaled.__ceil__() if upper else scaled.__floor__()
    sign = "-" if integer < 0 else ""
    digits = str(abs(integer)).rjust(places + 1, "0")
    return sign + digits[:-places] + "." + digits[-places:]


def interval(value, radius):
    return [decimal_out(value - radius),
            decimal_out(value + radius, upper=True)]


def run_certificate():
    """Verify both rational inverse certificates and persist their enclosures."""
    start = time.monotonic()
    data = load_data()
    # Retain both exact transcendental-constant bracket checks.
    epsilon = F(1, 10**36)
    al, au = atan_bracket(5)
    bl, bu = atan_bracket(239)
    assert PI - epsilon < 16*al - 4*bu <= 16*au - 4*bl < PI + epsilon
    assert (BETA - epsilon)**2 < F(3, 4) < (BETA + epsilon)**2

    weights = []
    points = []
    for v in range(N):
        alpha = F(2*v + 1, 2*N)
        weights.append(floor_rational(
            (1 - sum((2 * ereal(2*a*alpha).r / F(4*a*a - 1)
                      for a in range(1, N//2)), F(0))) / N))
        points.append(ereal(alpha).r)
    print("weights complete", time.monotonic() - start, flush=True)

    polynomial = [C(5), C(-1, 2*BETA), C(1, 2*BETA), C(-2),
                  C(-F(1, 2), BETA), C(-1, -2*BETA), C(1)]
    q_values = {1: 2*PI*PI*(2 - 2*BETA)/3,
                3: 2*PI*PI*(2 - 2*BETA)/3, 4: PI*PI/3}
    d_values = {1: PI*(2*BETA + 3)/18,
                3: -PI*(2*BETA + 3)/18, 4: 7*BETA*PI/9}
    matrix = [[F(0) for _ in range(6)] for _ in range(6)]

    for j in range(1, 7):
        tails = {}
        for n in J:
            a = C()
            b0 = C()
            for ell in range(j, 7):
                u = polynomial[ell] * ereal(F(ell*n, 6))
                a = a + u
                b0 = b0 + u * F(ell, 6)
            tails[n] = (a, b0)
        for v in range(N):
            t = (2*j - 1 + points[v]) / 12
            tt = C(t, H)
            lam = floor_complex(I / (BETA*tt))
            z = floor_complex(-B/tt - I*H)
            densities = []
            for n in J:
                phase = ereal(-t*n)
                a, b0 = tails[n]
                densities.append((phase*(-2*PI*PI)*(b0 - t*a),
                                  phase*(2*PI)*I*a))
            for ri, m in enumerate(J):
                g0 = lam * estar(z*m)
                g1 = g0 * I * PI * z
                for ci in range(6):
                    density = densities[ci % 3][ci // 3]
                    x0 = (density*g0).r * weights[v] / 6
                    x1 = (density*g1).r * weights[v] / 6
                    matrix[ri][ci] += -x0 / q_values[m]
                    matrix[ri + 3][ci] += (d_values[m]*x0 - x1) / q_values[m]
        print("piece", j, "complete", time.monotonic() - start, flush=True)

    result = {
        **provenance(data, __file__),
        "status": "pass",
        "arithmetic": "exact fractions.Fraction",
        "floor_decimal_places": 40,
        "constant_absolute_error_bound": "1e-36",
        "exponential_taylor_degree": 32,
        "exponential_squarings": 10,
        "entry_error_bound": "1e-12",
        "quadrature_N": N,
        "nodes": J,
        "order": ["c1", "c3", "c4", "d1", "d3", "d4"],
        "selected_d1_d1": interval(matrix[3][3], ENTRY_ERROR),
        "matrix_enclosures": [[interval(x, ENTRY_ERROR) for x in row]
                              for row in matrix],
        "W_checks": {},
    }
    for sign, integers in [(1, data["W_plus"]), (-1, data["W_minus"])]:
        w = [[F(x, 10000) for x in row] for row in integers]
        wnorm = max(sum(abs(w[i][j]) for i in range(6)) for j in range(6))
        error = [[F(i == j) - sum(
            w[i][k] * (F(k == j) - sign*matrix[k][j]) for k in range(6))
            for j in range(6)] for i in range(6)]
        residual = max(sum(abs(error[i][j]) for i in range(6))
                       for j in range(6))
        # ||W * (S_exact-S_finite)||_1 <= ||W||_1 * 6*entry_error.
        radius = wnorm * 6 * ENTRY_ERROR
        residual_upper = residual + radius
        assert residual_upper < F(3, 1000), (sign, "residual norm")
        inverse_upper = wnorm / (1 - residual_upper)
        assert inverse_upper < 32, (sign, "inverse norm")
        result["W_checks"][str(sign)] = {
            "W_column_norm": decimal_out(wnorm, upper=True),
            "residual_norm_enclosure": interval(residual, radius),
            "inverse_norm_upper": decimal_out(inverse_upper, upper=True),
        }
    result["elapsed_seconds"] = time.monotonic() - start
    write_result("sjj-rational.json", result)
    print(json.dumps({"status": result["status"],
                      "selected": result["selected_d1_d1"],
                      "W_checks": result["W_checks"],
                      "seconds": result["elapsed_seconds"]}, indent=2), flush=True)
    return result


def main():
    run_certificate()


if __name__ == "__main__":
    main()
