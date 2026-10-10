"""Exact rational interval checks for the UL5 larger-width segment proof.

No external package is needed. Trigonometric and hyperbolic series through
degree 20 have error <= 21*3**21/21! on |x|<=3 (since e**3 < 21).
All comparisons below use Fraction endpoints, not printed decimal values.
"""
from fractions import Fraction as F
from math import factorial, isqrt


class I:
    def __init__(self, a, b=None):
        if isinstance(a, I):
            self.a, self.b = a.a, a.b
        else:
            self.a, self.b = F(a), F(a if b is None else b)
        assert self.a <= self.b

    def __add__(self, other):
        other = I(other)
        return I(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.b, -self.a)

    def __sub__(self, other):
        return self + -I(other)

    def __rsub__(self, other):
        return I(other) + -self

    def __mul__(self, other):
        other = I(other)
        vals = [x*y for x in (self.a, self.b) for y in (other.a, other.b)]
        return I(min(vals), max(vals))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = I(other)
        assert not other.a <= 0 <= other.b
        return self * I(1/other.b, 1/other.a)

    def __rtruediv__(self, other):
        return I(other)/self

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        if n % 2 == 0 and self.a < 0 < self.b:
            return I(0, max(abs(self.a), abs(self.b))**n)
        vals = [self.a**n, self.b**n]
        return I(min(vals), max(vals))

    def cap(self, v):
        v = F(v)
        return I(min(self.a, v), min(self.b, v))

    def __repr__(self):
        return '[%.15g, %.15g]' % (float(self.a), float(self.b))


def series(x, odd, alternating):
    x = F(x)
    assert abs(x) <= 3
    val = sum(((-1)**(n//2) if alternating else 1)*x**n/F(factorial(n))
              for n in range(1 if odd else 0, 21, 2))
    err = F(21)*abs(x)**21/F(factorial(21))
    assert err < F('0.00000001')
    return I(val-err, val+err)


def sin(x): return series(x, True, True)
def cos(x): return series(x, False, True)
def sinh(x): return series(x, True, False)
def cosh(x): return series(x, False, False)


def sqrt(x):
    x = I(x)
    assert x.a >= 0
    scale = 10**20
    lo = isqrt(x.a.numerator*scale**2//x.a.denominator)
    hi = isqrt(x.b.numerator*scale**2//x.b.denominator) + 1
    return I(F(lo, scale), F(hi, scale))


r, w, lam, chi, bm = map(F, ['.22', '4.6', '.65', '.064', '.0163'])


def p(h):
    h = F(h)
    co, si = cos(w*h), sin(w*h)
    return 2*r*r*(1-(co+w*cosh(h)/sinh(h)*si)*co/(1+w*w))


def f(h):
    h = F(h)
    return r*r/(1+w*w)*(w*w-sin(w*h)**2/sinh(h)**2)


def g(h):
    h = F(h)
    return F('.75')*sinh(h)/h*(1+cosh(h))


def lc(h):
    return F(2)*F('.728')/3-F('.812')*F(h)/2


def budget(p, f, radius, cd):
    p, f, radius, cd = map(I, [p, f, radius, cd])
    return (1+chi)*f-chi*(p+bm)-((radius+p+bm)**2+(cd+bm)**2)/(4*lam)


rows = [
    ('.54', '.58', [11379,4367,2004,5141,7101,2190,1901]),
    ('.58', '.63', [10895,4500,1970,6216,8020,2278,2006]),
    ('.63', '.684',[10112,4593,1937,7539,8020,2348,2276]),
]
print('TABLE REPRODUCTION: all intervals multiplied by 100000')
for left, right, claim in rows:
    left, right = F(left), F(right)
    pv, fv = p(left), f(left)
    up = F('.01815')+1/(312*sinh(2*left)**2)
    rp = (right**2*g(right)*lc('.54')/3).cap('.0802')
    ro = (right**2*g(right)*lc(right/2)/3).cap('.0802')
    vals = [pv, fv, up, rp, ro, budget(pv, fv, rp, '.08'), budget(pv, fv, ro, '.08')]
    print(str(left), str(right), [v*100000 for v in vals])
    for j in [0,2,3,4]: assert vals[j].b <= F(claim[j], 100000), j
    for j in [1,5,6]: assert vals[j].a >= F(claim[j], 100000), j
    rounded = [F(x, 100000) for x in claim]
    rounded_budgets = [budget(rounded[0], rounded[1], rounded[j], '.08') for j in [3,4]]
    assert rounded_budgets[0].a > rounded[5]
    assert rounded_budgets[1].a > rounded[6]
    print('  budgets using only rounded table inputs:', rounded_budgets)
    assert rounded[5] > rounded[2]
    assert rounded[6] > F('.01815')

print('\nFINAL WIDTH REGIMES')
negd = r*r*(sqrt(1+w*w)-1)/(1+w*w)
assert negd.b < F('.00810')
print('negative d absolute bound:', negd)
pfloor = 2*r*r*(1-(1+sqrt(1+w*w*(1/F('.68')+F('.68')/3)**2))/(2*(1+w*w)))
assert pfloor.a > F('.077')
print('p floor for h >= pi/w:', pfloor)
fpi = r*r/(1+w*w)*(w*w-(w*F('.1')/sinh('.68'))**2)
f78 = I(r*r/(1+w*w)*(w*w-1/F('.85')**2))
assert min(fpi.a, f78.a) > F('.0431')
print('f lower bounds for [pi/w,.78] and [.78,.9]:', fpi, f78)
f90 = I(r*r/(1+w*w)*(w*w-1/F('1.024')**2))
p90 = 2*r*r*(1-(1-sqrt(1+w*w*F('1.3965')**2))/(2*(1+w*w)))
assert f90.a > F('.04413') and p90.b < F('.10882')
print('f floor and p ceiling for h>=.9:', f90, p90)
for label, pp, ff, dd, bclaim, sclaim, sinhfloor in [
    ('[pi/w,.9]', '.0968','.0431','.08810','.02005','.01912','1.819'),
    ('h>=.9, negative d', '.0968','.04413','.08810','.02115','.01853','2.94'),
    ('h>=.9, nonnegative d', '.10882','.04413','.08','.01916','.01853','2.94'),
]:
    bb = budget(pp, ff, '.0802', dd)
    ss = F('.01815')+1/(312*F(sinhfloor)**2)
    assert bb.a >= F(bclaim)
    assert ss <= F(sclaim)
    assert bb.a > ss
    print(label, 'budget', bb, 'cost ceiling', float(ss), 'slack >=', float(bb.a-ss))

for arg, lower in [('.78','.85'),('.9','1.024'),('1.36','1.819'),('1.8','2.94')]:
    assert sinh(arg).a > F(lower)
assert (cosh('.9')/sinh('.9')).b < F('1.3965')
print('\nAll exact rational interval assertions passed.')
