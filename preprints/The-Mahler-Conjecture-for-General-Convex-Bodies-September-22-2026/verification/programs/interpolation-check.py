#!/usr/bin/env python3
"""Exact rational checks for input.md's 16-node interpolation constants."""
from fractions import Fraction as Q
from math import factorial, prod
from decimal import Decimal, getcontext

getcontext().prec = 65
radius = Q(36, 100)
spacing = Q(1, 40)
strip_margin = Q(45, 100) - radius
profile_bound = Q(400000)
base_bound = Q(1300)

first_derivative = base_bound / strip_margin
second_derivative = 2 * base_bound / strip_margin**2
normalized_second = second_derivative + first_derivative
assert max(base_bound, first_derivative, second_derivative,
           normalized_second, Q(11000)) < profile_bound

remainder = profile_bound * prod(
    (spacing * Q(2*j+1, 2) / radius)**2 for j in range(8)
)
chord_terms = [
    prod(Q(2*j+1, 2)**2 for j in range(l-1))
    * Q(2**(2*l-4), factorial(2*l-2))
    for l in range(2, 9)
]
chord_factor = sum(chord_terms, Q(0))
assert remainder < Q(1, 100000)
assert chord_factor == Q(4387, 8192)
assert chord_factor < Q(536, 1000)

for name, value in [
    ("first_derivative_bound", first_derivative),
    ("second_derivative_bound", second_derivative),
    ("normalized_second_bound", normalized_second),
    ("remainder", remainder),
    ("remainder_margin", Q(1, 100000)-remainder),
    ("chord_factor", chord_factor),
    ("chord_margin", Q(536, 1000)-chord_factor),
]:
    print(f"{name}: {value} = {Decimal(value.numerator)/Decimal(value.denominator)}")
print("per-level chord terms:", ", ".join(map(str, chord_terms)))
print("PASS: all asserted rational inequalities hold.")

