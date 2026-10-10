#!/usr/bin/env python3
"""Independent exact scalar audit of the two Haldane purity bootstraps.

This checks scalar implications of the stated finite-input inequalities.
It does not compute those thermal matrices or trial-state contractions.
No floating-point calculation is used in any assertion.
"""

from fractions import Fraction as F
from math import comb


def f(u):
    assert 0 <= u < 1
    return u * u / (2 * (1 - u) ** 2)


def ceiling_grid(x, denominator=10**7):
    q = x * denominator
    return F(-(-q.numerator // q.denominator), denominator)


def coefficient(u):
    v = 1 - u
    return sum(v ** (-j) for j in (1, 2, 3)) ** 2 / 2


# Source 1: independently rebuild the input rational expressions.
table = [
    [124885379, 65757], [2925, 2960742], [12870614, 286599],
    [54069, 1920414], [4639283, 510140], [195455, 1514846],
    [2654823, 675419], [377629, 1314544], [1900547, 787405],
]
eps = F(30, 10**6)
moments = [[F(0)] * 4 + [F(z + k * p, 4 * 10**6) for z, p in table]
           for k in (3, -1)]
cap = [F(100139, 100000), F(872, 1000)]

# These checks are scalar consequences of the externally certified moments.
for r, coefficients in enumerate(([7, 17, -280, -185, 1000],
                                   [12, 0, -394, 0, 1000])):
    polynomial = [0] * 13
    for i, x in enumerate(coefficients):
        for j, y in enumerate(coefficients):
            polynomial[i + j + 4] += x * y
    upper = sum(p * m + abs(p) * eps for p, m in zip(polynomial, moments[r]))
    for sign in (-1, 1):
        translated = [sum(comb(i, j) * p * sign**i * cap[r]**(i-j)
                          for i, p in enumerate(polynomial) if i >= j)
                      for j in range(13)]
        assert translated[0] > upper
        assert all(x >= 0 for x in translated[1:])

up = [m[12] + eps for m in moments]


def capped(n, r, z):
    h = z**12
    whole = up[r] // h
    remainder = up[r] - whole * h
    assert 0 <= remainder < h
    return whole * z**n + remainder**(n // 12)


def non(n):
    return 3 * capped(n, 1, cap[1])


lo = F(999, 1000)
assert capped(72, 0, lo) + non(72) < 1
assert up[0] > lo**12


def tail(n):
    return non(n) + (up[0] - lo**12)**(n // 12)


p = 1 - (1 + tail(36) / lo**36)**(-2)
q = 1 - (cap[0]**72 + tail(72))**(-2)
assert 0 < p < 1 and 0 < q < 1
print('source1 initial p interval:', F(47915, 10**6), F(47916, 10**6))
print('source1 initial q interval:', F(181520, 10**6), F(181521, 10**6))
assert F(47915, 10**6) < p < F(47916, 10**6)
assert F(181520, 10**6) < q < F(181521, 10**6)

expected = [
    (F(151249, 2500000), F(433453, 2500000)),
    (F(343303, 5000000), F(1632381, 10000000)),
    (F(44601, 625000), F(361773, 2500000)),
    (F(632939, 10000000), F(1055161, 10000000)),
    (F(375793, 10000000), F(445941, 10000000)),
    (F(84513, 10000000), F(27493, 5000000)),
]
for j, pair in enumerate(expected, 1):
    exact_p = f(1 - (1 - p)**2 * (1 - q))
    p = ceiling_grid(exact_p)
    assert exact_p <= p < exact_p + F(1, 10**7)
    assert p < 1
    exact_q = f(1 - (1 - q)**2 * (1 - p))
    q = ceiling_grid(exact_q)
    assert exact_q <= q < exact_q + F(1, 10**7)
    assert q < 1
    assert (p, q) == pair
    print('source1 rounded round', j, p, q)
assert max(p, q) < F(1, 100)
assert 36 * 2**6 == 2304
assert F(49, 4) * 2**6 == 784

# Common envelope constants, both checked by exact rational arithmetic.
parameters = [('source1', F(1, 100), F(5), 2304, F(784)),
              ('source2', F(1, 8), F(79, 10), 60, F(105, 4))]
for name, u0, C, n0, b0 in parameters:
    G = coefficient(u0)
    assert 0 < u0 < F(1, 6)
    assert G < C
    assert C * u0 < 1
    assert C * (1 - 3 * u0) > 3
    ratio_factor = 3 / (C * (1 - 3 * u0))
    assert ratio_factor < 1
    assert (1 - u0)**3 > F(1, 2)
    print(name, 'G(u0)=', G, 'C-G=', C-G,
          'r=', C*u0, 'ratio factor=', ratio_factor)
    # Finite samples test the exact formula, the analytic induction is in the report.
    for j in range(7):
        u = (C*u0)**(2**j) / C
        next_u = (C*u0)**(2**(j+1)) / C
        assert next_u == C*u*u
        assert 0 < next_u <= u <= u0
        pnext = f(1-(1-u)**3)
        qnext = f(1-(1-u)**2*(1-pnext))
        assert pnext <= next_u and qnext <= next_u

assert coefficient(F(1, 8)) == F(913952, 117649)
assert F(79, 10) - coefficient(F(1, 8)) == F(154751, 1176490)
assert F(9, 2) / F(97, 100)**2 < 5
assert F(3, 5) / (1 - F(3, 5) * F(1, 20)) == F(60, 97) < 1
assert 3 / (F(79, 10)*(1-F(3, 8))) == F(48, 79) < 1
print('PASS: all exact scalar bootstrap assertions')
