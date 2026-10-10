#!/usr/bin/env python3
"""Check the finite combinatorial inequalities using exact arithmetic.

This does not instantiate the astronomically large finite Hilbert spaces.
All assertions use Python integers and require only the standard library.
"""
from math import comb, isqrt
import json
from pathlib import Path

p = 257
k = 4*p
K = k**3
A = sum(comb(k, j) for j in range(p))
b = comb(k-1, 2*p-1)
Q = b**3

assert all(p % r != 0 for r in range(2, isqrt(p)+1))
remainders = {str(r): p % r for r in (2, 3, 5, 7, 11, 13)}
assert list(remainders.values()) == [1, 2, 2, 5, 4, 10]
assert 2*b == comb(k, 2*p)
assert comb(k, 2*p)*(k+1) >= 16**p
assert A <= p*comb(k, p)
assert comb(k, p)*27**p <= 256**p
assert 256 < 12*27
assert 2*p*(4*p+1) < 2**20
assert p == 3*85+2
assert 27 < 32  # (3/4)^3 < 1/2
assert A*4**p < b*2*p*(4*p+1)*3**p
assert 2*p*(4*p+1)*3**p*2**65 < 4**p
assert k < 2**11
assert K < 2**33
assert 3 < 2**32  # 3*2^-65 < 2^-33
assert A*2**65 < b
assert 3*A*K < b
assert 3*A*b*b >= 3  # 3 delta Q, resolving vacuous singleton supports

# Largest integer m for which delta < 2^-m, checked without logarithms.
m = b.bit_length() - A.bit_length()
while (A << m) >= b:
    m -= 1
while (A << (m+1)) < b:
    m += 1
assert (A << m) < b <= (A << (m+1))

result = {
    'arithmetic': 'exact Python integers; all assertions passed',
    'p': p,
    'k': k,
    'K': K,
    'prime_check': 'trial division by every integer from 2 through isqrt(p)',
    'remainders': remainders,
    'prefactor_2p_4p_plus_1': 2*p*(4*p+1),
    'A': str(A),
    'b': str(b),
    'A_bit_length': A.bit_length(),
    'b_bit_length': b.bit_length(),
    'Q_bit_length': Q.bit_length(),
    'delta_less_than_2_pow_minus_65': A*2**65 < b,
    'three_delta_less_than_inverse_K': 3*A*K < b,
    'max_integer_m_such_that_delta_less_than_2_pow_minus_m': m,
    'three_delta_Q_at_least_three': 3*A*b*b >= 3,
}
output = Path(__file__).with_name('combinatorics_exact_checks.json')
output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
