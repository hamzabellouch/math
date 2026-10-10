"""Exact rational checks for the constants in input.md line 702.

This checks auxiliary numerical inequalities, not the finite profile tables.
The accompanying review supplies the analytic arguments.
"""

from fractions import Fraction as F
from math import factorial
import json


def exp_bounds(x, n=40):
    assert x >= 0 and x < n + 2
    partial = sum((x**j / factorial(j) for j in range(n + 1)), F(0))
    next_term = x ** (n + 1) / factorial(n + 1)
    return partial, partial + next_term / (1 - x / (n + 2))


def atan_bounds(x, n=40):
    assert 0 <= x <= 1
    partial = sum(((-1)**j * x**(2*j+1) / (2*j+1)
                   for j in range(n)), F(0))
    remainder = x ** (2*n+1) / (2*n+1)
    return ((partial, partial + remainder) if n % 2 == 0
            else (partial - remainder, partial))


a5, b5 = atan_bounds(F(1, 5))
a239, b239 = atan_bounds(F(1, 239))
pi_lo, pi_hi = 16*a5 - 4*b239, 16*b5 - 4*a239
assert F(25, 8) < pi_lo < pi_hi < F(63, 20)
assert F(5, 2)**2 < 2*pi_lo
assert 2*pi_hi < F('2.51')**2

beta = F('.45')
sin_upper = beta - beta**3/6 + beta**5/120
cos_lower = 1 - beta**2/2
assert sin_upper < F('.435')
assert F('3.6')**2 * sin_upper**2 < F('2.5')
assert sin_upper / cos_lower < F('.5')
assert F('.9')**2 * (F('2.5') + F('.25')*F('.9')**2) < (pi_lo/2)**2

assert exp_bounds(F('1.25'))[1] < F('3.5')
assert F('.5') - (F('.9') - F('.9')**3/6)/F('2.51') < F('.19')
assert exp_bounds(F('1.35125'))[1] < 4
assert F('.19') * 4 < F('.8')
assert exp_bounds(F(2))[1] < 8
assert F(1, 32) > F('.02')
assert F('.936')**2 > F(7, 8)
assert F('.324') * exp_bounds(F('1.125'))[1] < 1
assert (1 - F('.936')) * F('.324') > F('.02')

# The logarithmic estimates use monotonicity of exp.
assert exp_bounds(F('.925'))[0] > F('2.51')
assert exp_bounds(F(4))[0] > 50
assert exp_bounds(F('.7'))[0] > 2
j_constant = F('1.25') + F('.925') + 4 + F('1.575') + F('2.75')
assert j_constant == F('10.5')
bj_bound = F('.625') + F('.7') + F('10.5')
assert bj_bound < 12
assert F('1.254')**2 * bj_bound < 19
d_bound = 12 + F('3.75')**2 * F('2.5')
k_bound = 48 + 19 + F('1.254')**2 * F('2.75')**2 * F('2.5') + 1
xgp_bound = 2*(12 + F('3.75')*F('2.75')*F('2.5'))
assert d_bound < 48 and k_bound < 99 and xgp_bound < 76
c_bound = 48 + F('6.5') * (76+99)
assert c_bound < 1300
assert 7 * (F('1.25') + F('1.6')) < 20
assert 2 + 20 + 49 + 10000 < 11000

print(json.dumps({
    'status': 'all exact rational assertions passed',
    'bounds': {
        'd': str(d_bound),
        'K': str(k_bound),
        'xg_prime': str(xgp_bound),
        'C': str(c_bound),
        'R_v': '107',
        'V_2': '10071'
    }
}, indent=2))
