"""Supplementary exact rational checks for the half-line profile construction.

This is independent of certificate.py. All decimal strings below denote exact
rational numbers, and every asserted inequality is an exact Fraction comparison.
No floating point or transcendental evaluation is used.
"""
from fractions import Fraction as F


class I:
    def __init__(self, lo, hi=None):
        self.lo = F(lo)
        self.hi = F(lo if hi is None else hi)
        assert self.lo <= self.hi

    def __add__(self, other):
        other = other if isinstance(other, I) else I(other)
        return I(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-other if isinstance(other, I) else -F(other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        other = other if isinstance(other, I) else I(other)
        vals = [a * b for a in (self.lo, self.hi)
                for b in (other.lo, other.hi)]
        return I(min(vals), max(vals))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = other if isinstance(other, I) else I(other)
        assert not other.lo <= 0 <= other.hi
        return self * I(1 / other.hi, 1 / other.lo)

    def __rtruediv__(self, other):
        return I(other) / self

    def __pow__(self, power):
        assert power >= 0
        answer = I(1)
        for _ in range(power):
            answer = answer * self
        return answer

    def within(self, lo, hi):
        return F(lo) < self.lo <= self.hi < F(hi)

    def abs_upper(self):
        return max(abs(self.lo), abs(self.hi))


S = 56
A = F(15, S)
B = F(751, 4)
C = -F(1215, 4)
H = 1 + C / (2 * S**3)
beta = B / (2 * S**2)
D0 = lambda t: t**3 + A*t**2 + beta*t + H
assert A*A - 3*beta == -F(453, 25088)
assert D0(-F('1.08659')) == -F(17566501197647, 343000000000000000)
assert D0(-F('1.08655')) == F(187622583137, 2744000000000000)
r = I('1.08655', '1.08659')
u = (r - A) / 2
assert u.within('.40933', '.40938')
v2 = H/r - u*u
assert v2.within(F('.8671')**2, F('.86721')**2)
v = I('.8671', '.86721')
rho2 = H/r
assert rho2.hi < F('.959')**2
E = (r+u)**2 + v2
assert E.lo > F('2.9895')
assert F('1.729')**2 < F('2.9895')

# Rows are q, Re(xi), Im(xi), acting on (V,V',V'').
rows = [
    [rho2/E, -2*u/E, 1/E],
    [r*(r+2*u)/(2*E), u/E, -1/(2*E)],
    [r*(u*(r+u)-v2)/(2*v*E),
     -(v2+r*r-u*u)/(2*v*E), -(r+u)/(2*v*E)],
]
boxes = [
    [('.3074', '.3078'), ('-.2740', '-.2737'), ('.3344', '.3346')],
    [('.3461', '.3464'), ('.1368', '.1370'), ('-.1673', '-.1672')],
    [('-.0294', '-.0291'), ('-.3406', '-.3402'), ('-.2887', '-.2883')],
]
Lambda = [[F(n, 10**5) for n in row] for row in
          [[30756, -27384, 33447], [34622, 13692, -16724],
           [-2925, -34040, -28850]]]
for row, rowboxes, ref, limit in zip(rows, boxes, Lambda, ['.92', '.68', '.68']):
    for entry, (lo, hi), center in zip(row, rowboxes, ref):
        assert entry.within(lo, hi)
        assert (entry-center).abs_upper() < F('.001')
    assert sum(entry.abs_upper() for entry in row) < F(limit)

M = [r.hi**i/(r.lo*F('2.9895'))
     + F('.959')**i/(F('.40933')*F('.8671')*F('1.729'))
     for i in range(3)]
for value, limit in zip(M, ['1.96', '1.92', '1.88']):
    assert value < F(limit)
xi = 1/(2*F('.40933')*F('.8671')*F('1.729'))
assert xi == F(500000000000, 613674044347) < F('.82')

R = F(5, 10**10)
d0 = F('.400682721856639')
delta_d = F(721855+359157, 10**8)*R
d = I(d0-delta_d, d0+delta_d)
assert d.within('.40068272185', '.40068272187')
# Use the wider manuscript interval for all coefficient and derivative bounds.
d = I('.40068272185', '.40068272187')
a = C*d
b = a*a + 567*a
c3 = 2*a*b - a**3 + F(2025, 4)*b
c4 = b*b + 2*a*c3 - 3*a*a*b + a**4 + F(567, 2)*c3
da = I(C)
db = (2*a + 567)*da
dc3 = 2*da*b + 2*a*db - 3*a*a*da + F(2025, 4)*db
dc4 = (2*b*db + 2*da*c3 + 2*a*dc3 - 6*a*da*b - 3*a*a*db
       + 4*a**3*da + F(567, 2)*dc3)
coefficient_bounds = [122, 54200, 12500000, 5100000000]
derivative_bounds = [304, 100000, 65000000, 100000000000]
for coefficient, derivative, bound, dbound in zip(
        [a,b,c3,c4], [da,db,dc3,dc4], coefficient_bounds, derivative_bounds):
    assert coefficient.abs_upper() < bound
    assert derivative.abs_upper() < dbound
derivative_sum = sum(F(bound, S**(3*j))
                     for j, bound in enumerate(derivative_bounds, 1))
assert derivative_sum < F('.001735')
terms = [F('.00070'), F('.0000018'), F('.0000000081'), F('.000000000032')]
for j, (coefficient, coarse_bound, bound) in enumerate(
        zip([a,b,c3,c4], coefficient_bounds, terms), 1):
    assert coefficient.abs_upper()/S**(3*j) < bound
    assert F(coarse_bound, S**(3*j)) < bound

def shifted_linear(j):
    t = -3*j
    return t*(t-1)*(t-2)+30*t*(t-1)+B*t+C

assert [shifted_linear(j) for j in range(5)] == [
    C, -F(567), -F(2025,4), -F(567,2), -F(243,4)]
t1, t2, t3, t4 = terms
T = sum(terms)
tails = [T*T-t1*t1-2*t1*t2-2*t1*t3-t2*t2,
         T**3-t1**3-3*t1*t1*t2, T**4-t1**4]
for value, limit in zip(tails, [F(8,10**14), F(2,10**14), F(3,10**15)]):
    assert 0 < value < limit
assert T < F('.001')
higher = F('.001')**5/(1-F('.001'))
linear = F(243,4)*t4/S**3
assert higher < F(2,10**15)
assert linear < F(12,10**15)
assert sum(tails)+higher+linear < F(3,10**13)

assert T + (F('.26')+F('1.96')*F('.3'))*R < F('.001')
nonlinear_derivative = F('.001')*(2+F('.001'))/(1-F('.001'))**2
assert nonlinear_derivative < F('.0021')
lip = A*F('1.88') + beta*F('1.92') + (abs(C)/(2*S**3)+F('.0021'))*F('1.96')
stable = A*r.hi**2 + beta*r.hi + abs(C)/(2*S**3) + F('.0021')
assert lip == F(1777663401, 3136000000) < F('.57')
assert stable == F(3860747328989, 10976000000000) < F('.36')
assert F(3,10**13)/R+F('.36')*F('.26')+F('.57')*F('.3') == F('.2652') < F('.3')
assert F('.82')*F('.3') == F('.246') < F('.25')

print('All root, projection, convolution, coefficient, derivative, residual, and contraction checks passed exactly.')
print('Projection entry enclosures:', boxes)
print('Convolution rational bounds:', [str(value) for value in M])
print('Nonreal response bound:', xi)
print('Coefficient bounds on the wider d interval:', coefficient_bounds)
print('Parameter-derivative bounds on the wider d interval:', derivative_bounds)
print('Asymptotic parameter-derivative sum bound:', derivative_sum)
print('Lipschitz bound:', lip)
print('Stable-mode bound:', stable)
