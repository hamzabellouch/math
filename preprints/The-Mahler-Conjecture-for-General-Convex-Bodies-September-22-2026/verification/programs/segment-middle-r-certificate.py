#!/usr/bin/env python3
"""Exact rational audit of input.md's middle-width R cubic table.

Only display formatting uses Decimal. All certificates use Fraction and isqrt.
Every irrational square root is enclosed between rationals of width 10^-80.
"""
from decimal import Decimal, localcontext
from fractions import Fraction as F
from math import isqrt


def sqrt_interval(x):
    scale = 10**80
    k = isqrt(x.numerator * scale**2 // x.denominator)
    lo, hi = F(k, scale), F(k + 1, scale)
    assert lo * lo <= x < hi * hi
    return lo, hi


def dec(x):
    with localcontext() as ctx:
        ctx.prec = 30
        return str(Decimal(x.numerator) / Decimal(x.denominator))


r, w, lam, chi = map(F, ['.22', '4.6', '.65', '.064'])
knots = list(map(F, ['.16', '.23', '.29', '.35', '.40', '.45', '.50', '.54']))
rows = [
    [8298, 12885, 12902, 1576, 20047, 2028],
    [13121, 16655, 16699, 1851, 26748, 2449],
    [15242, 18360, 18453, 2069, 31598, 2526],
    [15218, 18414, 18572, 2208, 35687, 2308],
    [15449, 18673, 18925, 2309, 38555, 2242],
    [15768, 19010, 19395, 2370, 40970, 2218],
    [16025, 19288, 19811, 2390, 42963, 2195],
]


def lc(h):
    return 2 * F('.728') / 3 - F('.812') * h / 2


def gu(h):
    return F('.75') * (1 + h*h/6 + F('.0084')*h**4) * (2 + h*h/2 + F('.0421')*h**4)


print('Computed coefficient upper bounds and exact N0, all scaled by 100000:')
for L, H, row in zip(knots, knots[1:], rows):
    su = 1 + H**2 / 6 + F('.0084') * H**4
    hu = 1 + H**2 / 2 + F('.0421') * H**4
    p1 = r*r*w*w*H*H*(F(4)/3 + F('.05')*H*H)
    rad = 1 + w*w*(1/L + L/3)**2
    sqlo, sqhi = sqrt_interval(rad)
    p2lo = 2*r*r*(1 - (1-sqlo)/(2*(1+w*w)))
    p2hi = 2*r*r*(1 - (1-sqhi)/(2*(1+w*w)))
    a0lo = gu(H)*H*H*lc(H)/3 + min(p1, p2lo)
    a0hi = gu(H)*H*H*lc(H)/3 + min(p1, p2hi)
    assert 0 <= a0hi-a0lo < F(1,10**80)
    qhi = chi + (2*a0hi + F('.05')*H*H)/(4*lam)
    ahi = qhi + H**4/(25*lam)
    b = H*(F('.281')-F('.254')*H)/(5*lam)
    n = F('.855')*L*(1-L+L*L/3-F('.023')*L**4)/(3*F('.193'))
    rounded = [F(x,100000) for x in row]
    for true_upper, published_upper in zip([a0hi,qhi,ahi,b], rounded[:4]):
        assert true_upper <= published_upper
    assert rounded[4] <= n
    assert p1 <= p2lo if H <= F('.29') else p2hi < p1
    qr, ar, br, nr = rounded[1:5]
    zrad = ar*ar + 3*nr*br
    zslo, zshi = sqrt_interval(zrad)
    zlo, zhi = (ar+zslo)/(3*nr), (ar+zshi)/(3*nr)
    # On Z >= 0, derivative B+2AZ-3NZ^2 has just one nonnegative root.
    # There the cubic value is Q/25+(A Z^2+2 B Z)/3, increasing in Z.
    maxlo = qr/25 + (ar*zlo*zlo+2*br*zlo)/3
    maxhi = qr/25 + (ar*zhi*zhi+2*br*zhi)/3
    assert maxhi < rounded[5] < F('.027')
    print(f'[{dec(L)}, {dec(H)}]:', ', '.join(dec(v*100000) for v in [a0hi,qhi,ahi,b,n]))
    print('  rounded-cubic maximum <=', dec(maxhi),
          '; published-cost slack >=', dec(rounded[5]-maxhi))

# Auxiliary constants needed by the reduction of the square and variance term.
assert 1-(max(F(row[0],100000) for row in rows)+F('.0163'))/(2*lam) >= F('.855')
assert F('.193')**2 + knots[-1]**2/25 < F('.05')
assert F('.53') * gu(knots[-1]) / (F('1.5')*3) < F(1,5)
assert F('.79') * gu(knots[-1]) / (F('1.5')*3) < F('.33')
assert knots[0]*(F('.281')-F('.254')*knots[0]) > F('.032')
print('All exact coefficient, cubic-maximum, and reduction-constant assertions passed.')
