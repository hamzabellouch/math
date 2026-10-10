"""Independent exact-rational checks of the proof's analytic allowances.

These checks are separate from, and do not replace, certificate.py.
All comparisons use Fraction. Decimal output is descriptive only.
Positive exponentials are bounded above by a rational Taylor sum and
geometric bound for its positive remainder.
"""
from fractions import Fraction as F
from decimal import Decimal, localcontext
import json
from pathlib import Path


def exp_upper(x, degree=80):
    x = F(x)
    term = total = F(1)
    for j in range(1, degree + 1):
        term *= x / j
        total += term
    first_omitted = term * x / (degree + 1)
    ratio_bound = x / (degree + 2)
    assert 0 <= ratio_bound < 1
    return total + first_omitted / (1 - ratio_bound)


def dec(x):
    with localcontext() as c:
        c.prec = 22
        return str(Decimal(x.numerator) / Decimal(x.denominator))


R = F(5, 10**10)
out = {}
majorant = F('0.585') + F(9, 440) * (1 + 1 / (F('1.30') - F('.8')))
assert majorant < F('.8')
out['origin_series_majorant'] = majorant
origin_tail = F('.8') * (F('1.5') * 61) ** 2 / 3**61
t = F('.11') * R
parameter_tail = 2 * (1 / (1 - t) ** 2 - 1 - 2 * t)
# Cauchy differentiated origin tails contribute at most .12*tail per
# parameter-row sum: 10 times the sum of the two parameter-map row norms.
# Include both rounded first-variation columns and midpoint grid units.
origin_error = (F(5, 10**21) + origin_tail + parameter_tail
                + F('.12') * origin_tail * R + F(1, 10**20) * R
                + F(3, 2**256))
assert origin_error < F(2, 10**19)
out.update(origin_jet_tail=origin_tail, parameter_taylor_tail=parameter_tail,
           initial_error_upper=origin_error)

e = exp_upper(F('.954') / 2)
base = F('.01') + (F('.190') * F('.06') + F('.011') * F('1.3')
                         + F('.015625') * F('.86') / F('.14')) / 2
linear = F('.190') / 4
h2 = e * base / (1 - e * linear)
assert h2 < F('.13')
out['H2_upper'] = h2
disk_displacement = F('.06') / 2 + F('.13') / 8
real_displacement = F('.06') / 8 + F('.13') / (2 * 8**2)
assert disk_displacement < F('.1') and real_displacement < F('.01')
out.update(disk_displacement=disk_displacement, real_substep_displacement=real_displacement)

complex_jacobian = F(30) / F('31.5') + F(751, 4) / F('31.5') ** 2 + F(1215, 2) / F('31.5') ** 3 + F(1, 64) / F('.14') ** 2
assert complex_jacobian < F('2.1')
variation = 6 * exp_upper(F('2.1') / 2)
assert variation < 32
tail = F(32) * F(1, 4)**45 / (1 - F(1, 4))
allowance = F(48) * F(1, 4)**45
assert tail < allowance
out.update(complex_jacobian_norm=complex_jacobian, variation_entry_upper=variation,
           cauchy_tail_upper=tail, code_tail_allowance=allowance)

real_jacobian = F(30, 32) + F(751, 4) / 32**2 + F(1215, 2) / 32**3 + F(1, 64) / F('.23')**2
partial_transfer = exp_upper(real_jacobian)
assert partial_transfer < F('4.3')
product_error = 8500 * ((1 + F(4, 10**15) * 8500)**288 - 1)
assert product_error < F('.001')
assert 570000 + 288 * F('.001') < 580000
assert 246000 + F(55) * F('.001') / F('.23')**3 < 250000
out.update(real_jacobian_norm=real_jacobian, partial_transfer_upper=partial_transfer,
           all_product_error_upper=product_error)

endpoint_error = 580000 * F(1, 10**19) + 8501 * F(2, 10**19) + F('4.3') * 250000 * F('1.001') * (14 * R)**2
intermediate = F('4.3') * (F('2.72') + F('.11')) * R + F('4.3') * F('1.001') * (14 * R)**2 / F('.23')**3
assert endpoint_error < F('.11') * R and intermediate < 14 * R
out.update(endpoint_error_in_R=endpoint_error / R, intermediate_error_in_R=intermediate / R)
for name, b0, b1, limit in [('real', F('.116'), F('.92'), F('.25')), ('complex_rows', F('.001'), F('.68'), F('.13'))]:
    value = F('.006') + F('.003') * F('.04') + b0 + F('.003') * F('2.7') + b1 * (F('.11') + F('.001') * F('.02') + F('.01') * F('.011'))
    assert value < limit
    out[name + '_projection_error_in_R'] = value

report = {'all_exact_rational_checks_pass': True,
          'values_decimal_descriptive_only': {k: dec(v) for k, v in out.items()}}
dest = Path(__file__).with_suffix('.json')
dest.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
