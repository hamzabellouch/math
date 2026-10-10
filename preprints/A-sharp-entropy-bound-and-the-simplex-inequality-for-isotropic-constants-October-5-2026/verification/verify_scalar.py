#!/usr/bin/env python3
"""Reproduce the scalar certificate using only Python's standard library.

Run: python3 verification/verify_scalar.py

All input decimals, polynomial operations, enclosures, and comparisons are exact
fractions. Printed decimals are rounded OUTWARDS; no float is used. No sampling,
numerical integration, external data, or imported certificate module is used.

Mathematical inputs, proved in the accompanying scalar appendix, are the Mills
alternating-integral bounds, the Gaussian ODEs, their contractive error comparison,
the quartic Bernstein enclosure, the elementary integral tail estimates, and the
multi-affine corner principle. This program checks their rational hypotheses and
consequences; it is not a formal proof assistant for those calculus statements.
"""

from fractions import Fraction as F
from itertools import product
from math import comb, factorial


def q(value):
    """Reject binary floating-point input, including in future table edits."""
    if isinstance(value, float):
        raise TypeError("Use a decimal string, integer, or Fraction")
    return F(value)


def require(condition, message):
    # Deliberately not assert: verification also works under python -O.
    if not condition:
        raise ArithmeticError(message)


def down(value, places=12):
    n = value.numerator * 10**places // value.denominator
    sign = "-" if n < 0 else ""
    n = abs(n)
    return f"{sign}{n // 10**places}.{n % 10**places:0{places}d}"


def up(value, places=12):
    n = -((-value.numerator * 10**places) // value.denominator)
    sign = "-" if n < 0 else ""
    n = abs(n)
    return f"{sign}{n // 10**places}.{n % 10**places:0{places}d}"


def parse_rows(data):
    return [[None if x == "-" else q(x) for x in line.split()]
            for line in data.strip().splitlines()]


ROWS = parse_rows("""
-5.25 .75 .0000004128471303 .1842076703035094
-3.75 .75 .0003526268606772 .2507500253088710
-2.5 .5 .0176378254869167 .3531628936050266
-1.5 .5 .1387897504588508 .4981884857033017
-.5 .5 .5091604338370335 .7246172144765372
.25 .25 .9635539794164037 .9475979387933716
1.25 .75 1.7288166273310539 1.3000948982566192
3 1 3.2830986549304364 2.0126493036044195
5 1 5.1865039671258417 2.9046537878842420
7 1 7.1375456132265036 3.8366560415481663
9 1 9.1085231050028685 4.7898159350739631
""")

# b_min, b_max, L_max, D_max, K_min, K_max, J_max, L_1, m_0.
BINS = parse_rows("""
0 .09 .60 - .37 .56 .72 .13 0
.083 .15 1.01 4.3 .29 .46 .72 .13 .19
.14 .23 1.19 3 .29 .371 .68 .13 .38
.22 .342 1.19 1.72 .29 .398 .61 .123 .68
.337 .45 .83 .87 .31 .4 .50 .060 .68
.445 .5 .20 .640 .32 .4 .48 .022 .68
""")
CLAIMED = [[v / 1000 for v in row] for row in parse_rows("""
7 1 1 1
1 1 2 2
2 2 2 5
2 2 2 8
2 3 5 14
2 2 8 11
2 .8 8 20
2 .8 8 7
1 .8 10 15
3 .6 11 11
2 .35 12 9
""")]

ALPHA, BETA, S, GAMMA, DS = F(3, 40), F(7, 25), F(40, 37), F(3, 4), F(5, 17)
ASTAR = S + 1 + S / 8
MSTAR = S * BETA + (1 + S / 8) * GAMMA
MPRIME = S * BETA**2 + (9 * S / 8) * GAMMA**2
EQ, EK = F(1, 10**8), F(8, 10**7)


def add(a, b):
    out = [F(0)] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] += x
    return out


def scale(a, c):
    return [x * q(c) for x in a]


def sub(a, b):
    return add(a, scale(b, -1))


def mul(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def norm(a):
    return sum(map(abs, a), F(0))


def endpoint(a, x):
    return sum((v * x**i for i, v in enumerate(a)), F(0))


class Quartic:
    """Pair (polynomial, uniform error) on [-1,1], as in the appendix."""

    def __init__(self, f, error=0):
        f = f if isinstance(f, list) else [q(f)]
        self.f = (f + [F(0)] * 5)[:5]
        self.error = q(error) + norm(f[5:])

    def __add__(self, other):
        other = as_quartic(other)
        return Quartic(add(self.f, other.f), self.error + other.error)

    __radd__ = __add__

    def __neg__(self):
        return Quartic(scale(self.f, -1), self.error)

    def __sub__(self, other):
        return self + -as_quartic(other)

    def __rsub__(self, other):
        return as_quartic(other) + -self

    def __mul__(self, other):
        other = as_quartic(other)
        error = (norm(self.f) * other.error + norm(other.f) * self.error
                 + self.error * other.error)
        return Quartic(mul(self.f, other.f), error)

    __rmul__ = __mul__

    def __truediv__(self, constant):
        return self * (1 / q(constant))

    def __pow__(self, n):
        result = Quartic(1)
        for _ in range(n):
            result = result * self
        return result

    def lower(self):
        return min(sum((F(comb(i, j), comb(4, j)) * eta**j * self.f[j]
                        for j in range(i + 1)), F(0))
                   for i in range(5) for eta in (-1, 1)) - self.error


def as_quartic(value):
    return value if isinstance(value, Quartic) else Quartic(value)


def polynomials(row):
    w, r, p0, k0 = row
    a = [w, r]
    p, k = [F(0)] * 15, [F(0)] * 15
    p[0], k[0] = p0, k0
    for i in range(14):
        d = sub(p, a)
        p[i + 1] = r * mul(p, d)[i] / (i + 1)
        k[i + 1] = r * ((1 if i == 0 else 0) - mul(k, d)[i]) / (i + 1)
    d = sub(p, a)
    b = sub([F(1)], mul(k, d))
    j = add(sub(k, p), mul(a, b))
    y = add(sub(scale(b, 2), mul(p, d)), mul(a, j))
    eb = norm(k) * EQ + EK * (EQ + norm(d))
    ej = EQ + EK + norm(a) * eb
    ey = 2 * eb + (norm(p) + norm(d) + EQ) * EQ + norm(a) * ej
    # Construct FULL b,j,y before the quartic truncation, as specified.
    approximants = [Quartic(p, EQ), Quartic(k, EK), Quartic(d, EQ),
                    Quartic(b, eb), Quartic(j, ej), Quartic(y, ey), Quartic(a)]
    return approximants, (p, k, d)


def groups(row, approximants):
    w = row[0]
    idx = (0 if w < -3 else 1 if w < -2 else 2 if w < -1
           else 3 if w < F(1, 2) else 4 if w < 4 else 5)
    bmin, bmax, lmax, dmax, kmin, kmax, jmax, l1, m0 = BINS[idx]
    zmin, zmax, chimax = map(q, ("-.08", ".7", ".07") if w < -1
                          else ("-.475", "0", ".097"))
    qq, k, d, b, l, lp, a = approximants
    p = b + k * l - l * l / ALPHA
    e = p + b * (q(".75") - b) - l * l / ALPHA
    hp = l + 3 * b * l + k * lp
    g1 = [b - bmin, bmax - b, l, ALPHA * lmax - l,
          p * (7 + a * a) - 1 if w < 0 else p - q(".46" if idx == 5 else ".25"),
          q(".67")**2 * p - (k * (b - q(".5")) - (b - q(".28")) * l * (2 / ALPHA))**2]
    g2 = [lp - zmin * l, zmax * l - lp, hp - q(".8") * l,
          q("1.77") * l - hp, chimax * d - l,
          2 * (1 - qq * d) * (1 - b * b) - 2 * b * l * d - m0 * d * d * (1 - b * b)]
    g3 = [DS * e - kmin * p, kmax * p - DS * e, jmax * p - DS * q("1.5") * b]
    if dmax is not None:
        g3.append(p - DS / dmax)
    f1 = q("1.5") * b
    h = q(".43") - l1 - ASTAR * b * b + MSTAR * b - MPRIME / 4 - l * l / ALPHA
    v = q("1.97") - MPRIME
    o = q(".13") - MPRIME / 2 + MSTAR * b
    g4 = [h * p - DS * e * e,
          p * (h * v - o * o) - DS * (e * e * v - 2 * e * o * f1 + h * f1 * f1)]
    return [g1, g2, g3, g4]


def atan_interval(x, n=24):
    """Alternating atan series, 0<x<1; n terms, then one more."""
    a = sum(((-1)**i * x**(2*i + 1) / (2*i + 1) for i in range(n)), F(0))
    b = a + (-1)**n * x**(2*n + 1) / (2*n + 1)
    return min(a, b), max(a, b)


def log_interval(x, n=36):
    """atanh expansion with range reduction; positive rational x only."""
    if x < 1:
        lo, hi = log_interval(1 / x, n)
        return -hi, -lo
    shifts = 0
    while x >= 2:
        x /= 2
        shifts += 1

    def unit(v):
        z = (v - 1) / (v + 1)
        lo = 2 * sum((z**(2*i + 1) / (2*i + 1) for i in range(n)), F(0))
        hi = lo + 2 * z**(2*n + 1) / ((2*n + 1) * (1 - z*z))
        return lo, hi

    lo, hi = unit(x)
    l2, h2 = unit(F(2))
    return lo + shifts * l2, hi + shifts * h2


def mills(r, n):
    double_factorial, total = 1, F(0)
    for i in range(n + 1):
        if i:
            double_factorial *= 2 * i - 1
        total += F((-1)**i * double_factorial, r**(2*i + 1))
    return total


def anchors():
    a5, a239 = atan_interval(F(1, 5)), atan_interval(F(1, 239))
    pi_lo, pi_hi = 16 * a5[0] - 4 * a239[1], 16 * a5[1] - 4 * a239[0]
    require(F(3) < pi_lo < pi_hi < F(22, 7), "Machin pi interval")
    # theta0=log(10 sqrt(2 pi))=log(200 pi)/2.
    theta_lo = log_interval(200 * pi_lo)[0] / 2
    theta_hi = log_interval(200 * pi_hi)[1] / 2
    require(q("3.221") < theta_lo < theta_hi < q("3.222"), "theta0 interval")
    print("theta0 enclosure:", down(theta_lo), "< theta0 <", up(theta_hi))
    # sqrt(2pi)>12/5 and e^18 exceeds this positive Taylor sum.
    exp18_lo = sum((F(18**i, factorial(i)) for i in range(60)), F(0))
    require(2*pi_lo > F(12, 5)**2, "sqrt(2pi)>12/5")
    require(F(5, 12) / exp18_lo < F(7, 10**9), "f6<7e-9")
    q_lo, q_hi = 1 / mills(10, 12), 1 / mills(10, 11)
    q_error = max(abs(q("10.098093234") - v) for v in (q_lo, q_hi))
    require(q_error < F(4, 10**10), "q(10) Mills anchor")
    # |k(-6)-I0(6)| <= 2 f6/36 < 7/(18*10^9).
    k_lo = mills(6, 13) - F(7, 18 * 10**9)
    k_hi = mills(6, 14) + F(7, 18 * 10**9)
    k_error = max(abs(q(".16237766") - v) for v in (k_lo, k_hi))
    require(k_error < F(4, 10**8), "k(-6) Mills anchor")
    print("Mills anchor absolute errors <=", up(q_error, 15), "and", up(k_error, 15))
    print("Machin pi, logarithm series, Gaussian-density bound, Mills anchors: PASS")


def central():
    previous = None
    residual_q = residual_k = jumps_q = jumps_k = forcing_k = F(0)
    min_d = F(100)
    points = {}
    print("Central quartic group lower bounds (rounded down):")
    for ri, row in enumerate(ROWS):
        w, r = row[:2]
        approximants, (p, k, d) = polynomials(row)
        rp, rk = r * norm(mul(p, d)[14:]), r * norm(mul(k, d)[14:])
        require(rp < (F(2, 10**9) if ri == 1 else F(7, 10**11)), "P residual")
        require(rk < F(2, 10**10), "Q residual")
        residual_q += 2 * rp
        residual_k += 2 * rk
        forcing_k += 2 * r * EQ * norm(k)
        d_lower = Quartic(d).lower()
        require(d_lower > q(".09"), "D polynomial positive")
        min_d = min(min_d, d_lower)
        require(norm(k) < (2 if w <= F(1, 4) else q("5.6")), "Q coefficient norm")
        if previous is not None:
            old_row, old_p, old_k = previous
            require(old_row[0] + old_row[1] == w - r, "contiguous intervals")
            jq = abs(endpoint(old_p, 1) - endpoint(p, -1))
            jk = abs(endpoint(old_k, 1) - endpoint(k, -1))
            require(jq < F(2, 10**10) and jk < F(2, 10**10), "joining errors")
            jumps_q += jq
            jumps_k += jk
        else:
            require(w - r == -6, "left endpoint")
            k_poly_anchor = abs(endpoint(k, -1) - q(".16237766"))
            require(k_poly_anchor < F(3, 10**9), "left Q anchor")
        previous = row, p, k
        for side in (-1, 1):
            points[w + r * side] = endpoint(p, side)
        lows = [min(v.lower() for v in group) for group in groups(row, approximants)]
        require(all(v >= c for v, c in zip(lows, CLAIMED[ri])), f"groups at w={w}")
        print(f"  {str(w):>5}:", " ".join(down(v) for v in lows))
    require(ROWS[-1][0] + ROWS[-1][1] == 10, "right endpoint")
    q_poly_anchor = abs(endpoint(p, 1) - q("10.098093234"))
    require(q_poly_anchor < F(2, 10**10), "right P anchor")
    q_budget = F(4, 10**10) + q_poly_anchor + jumps_q + residual_q
    k_budget = F(4, 10**8) + k_poly_anchor + jumps_k + residual_k + forcing_k
    require(q_budget < EQ and k_budget < EK, "global ODE error budgets")
    print("44 central group bounds, 22 residuals, 20 joins, 11 D bounds, 11 Q norms: PASS")
    print("D polynomial uniform lower bound >=", down(min_d))
    print("Endpoint polynomial anchor errors <=", up(q_poly_anchor, 15), "and", up(k_poly_anchor, 15))
    print("Integrated k forcing <=", up(forcing_k, 15))
    print("Global ODE error budgets <=", up(q_budget, 15), "< 1e-8;", up(k_budget, 15), "< 8e-7")
    require(points[-1] - EQ > q(".287"), "q(-1)>.287")
    require(points[-2] + EQ < q(".056"), "q(-2)<.056")
    require(points[-3] + EQ < q(".005"), "q(-3)<.005")
    require(points[4] - EQ > 4, "q(4)>4")
    for ratio, bound in [(F(287, 56), q("1.62")), (F(4)/q(".056"), F(4)),
                         (F(287, 5), F(4)), (F(4)/q(".005"), q("6.5"))]:
        require(log_interval(ratio)[0] > bound, "secant log length")
    print("Four q endpoint bounds and four secant logarithmic lengths: PASS")


def left_tail():
    u = F(1, 36)
    eta = 1 + u / 100
    b_over_u_lo = 1 - q("3.01") * u
    kl_over_b = 2 * u * eta**2 / b_over_u_lo
    l2_over_alpha_b = 4 * u**2 * eta**2 / (ALPHA * b_over_u_lo)
    require(eta * u < q(".028"), "left b upper")
    require(2 * eta / (216 * ALPHA) < q(".60"), "left L upper")
    require(1 / (1 + kl_over_b) > q(".93"), "left b/p lower")
    require(1 / (1 - l2_over_alpha_b) < q("1.05"), "left b/p upper")
    require(q("3.01") + 4 * u * eta**2 / ALPHA < q("4.54"), "left p lower")
    require((1 - q("4.54") * u) * (1 + 7 * u) > 1, "left p inverse quadratic")
    require(eta / 2 < q(".501"), "left h0 first magnitude")
    require(4 * BETA * eta * u / ALPHA < q(".43"), "left h0 second magnitude")
    require(q(".501")**2 < q(".67")**2 * (1 - q("4.54") * u), "left h0 bound")
    require(DS * (1 + q(".93") * (q(".75") - q(".028") - l2_over_alpha_b)) > q(".37"), "left K lower")
    require(DS * (1 + q("1.05") * q(".75")) < q(".56"), "left K upper")
    require(DS * q("1.5") * q("1.05") < q(".72"), "left J upper")
    require(DS < q(".295"), "left D upper coefficient")
    require(3 * F(1, 6) * eta / (1 - q("6.01") * u) < q(".61"), "left z upper")
    require(1 + 3 * q(".028") + eta * q(".61") / 6 < q("1.77"), "left hstar upper")
    require(2 * eta * u*u < q(".07"), "left chi upper")
    # All f(r)*r^n used here decrease for r>=6 (n<=7). Check at r=6.
    f6 = F(7, 10**9)
    gaussian_errors = [2*f6/36, 4*f6/6, 6*f6, 54*f6]
    for j, err in enumerate(gaussian_errors):
        require(err < F(1, 100) * u * F(factorial(j), 6**(j+1)), "left Gaussian correction")
    qd = q("1.01") * f6 * (6 + q("1.01") * f6)
    bld = q(".028") * (2 * eta / 216) * (6 + q("1.01") * f6)
    require(2 * (1-qd) * (1-q(".028")**2) - 2*bld > 0, "left log M derivative")
    require(q(".028") * (1 + kl_over_b + q(".75")) < q(".05072"), "left E upper")
    sub11 = ASTAR*q(".028")**2 + MPRIME/4 + (2*eta/216)**2/ALPHA + q(".56")*q(".05072")
    sub22 = MPRIME + q(".72") * q("1.5") * q(".028")
    require(sub11 < q(".224") and sub22 < q(".802"), "left matrix diagonals")
    require(q("1.5") * q(".56") < MSTAR, "left offdiagonal correction nonpositive")
    require(MPRIME/2 - MSTAR*q(".028") > q(".34") and MPRIME/2 < q(".386"), "left matrix offdiagonal")
    margin = (q(".43")-q(".224")-q(".13")) * (q("2.72")-q(".802")-q(".75")) - (q(".13")-q(".386"))**2
    require(margin > 0, "left matrix determinant")
    print("Left-tail Gaussian corrections and sufficient scalar/matrix margins: PASS")
    print("Left-tail determinant margin =", down(margin))


def right_tail():
    # H=(F1-1)/(2u)=1/2 integral_0^1 F1'(tu)dt.
    # For F1 log F1, use .99<=F1<=1 and 0<=1+log F1<=1.
    g2 = 15 + 6 + F(100, 99)
    g3 = 315 + 90 + 18*F(100, 99) + F(100, 99)**2
    require(g2 < 23 and g3 < 435, "G1 derivative bounds")
    print("G1 derivative upper bounds <=", up(g2), "< 23;", up(g3), "< 435")
    tlo, thi = q("3.221"), q("3.222")
    g0, c0 = q("11.5") + 3*thi, 435 + 90*thi
    ab, aj, ce = 3*thi-q("8.5"), 12*thi-37, 197-60*thi
    # x=log(r/10), u=.01 exp(-2x), theta=theta0+x. For linear
    # times exponential, locate its sole critical point then use
    # exp(-t)<=1/(1+t). The higher-order remainder terms decrease.
    require(0 < ab < F(3, 2) and 0 < aj < 6 and ce > 0, "tail critical point ranges")
    require(15 < 4*(5*g0+3) and 90 < 4*(30*g0+33)
            and 630 < 4*(210*g0+321) and 90 < 6*c0, "decreasing tail remainders")
    errb = q(".015") / (2 - 2*ab/3) + (5*g0+3)/10000
    errj = q(".06") / (2-aj/6) + (30*g0+33)/10000
    erre = max((197-60*tlo)/100, q(".3") / (2+ce/30)) + (210*g0+321)/10000 + 8*c0/1000000
    require(errb < q(".04") and errj < q(".13") and erre < q(".75"), "right error bounds")
    print("Right-tail B,J,E error upper bounds <=", up(errb), up(errj), up(erre))
    # These derivative-sign checks extend the following endpoint bounds to
    # every x>=0, where theta=theta0+x and u=.01 exp(-2x).
    require(1 < 2*(tlo-q("1.46")), "decreasing u B upper")
    require(2 < 3*(2*tlo-q("3.87")), "decreasing J/r^3 upper")
    require(1 < 2*(tlo-q(".475")), "decreasing u C upper")
    require(1/(tlo-q(".475")) + 2/(2*tlo-q("3.87")) < 2,
            "decreasing u C J upper")
    require(1 < tlo-q("1.46"), "decreasing B/r upper")
    require((thi-q("1.46"))/10 < q(".18"), "right B/r upper")
    # C1=theta-.5+(2.5-theta)u+R0, |R0|<=g0 u^2.
    # The upper correction is negative since both coefficients in
    # 2.5-theta+.01*(11.5+3theta) decrease with theta.
    require(q("2.5")-tlo+(q("11.5")+3*tlo)/100 < 0, "right C1 upper")
    require(q(".99")*tlo-q(".5")-(q("11.5")+3*thi)/10000 > 0,
            "right C1 positive")
    require((6*tlo-q("14.75"))/(2*tlo-q("3.87")) > q("1.7"), "right E/J lower")
    require(-q("13.25") < -3*q("4.13"), "right E/J upper 3")
    require(q(".5")-(thi-q("1.46"))/100 > q(".482"), "right b lower")
    require((2*thi-q("3.87"))/1000 < q(".0026"), "right l upper")
    require(q(".5")+(thi-q(".475"))/100 < q(".528"), "right k/r upper")
    require((thi-q(".475"))*(2*thi-q("3.87"))/100 < q(".075"), "right u C1 J upper")
    require(q(".5")-q(".605")/100-q(".0026")**2/ALPHA > q(".493"), "right p lower")
    require(-q(".395")+q(".075") < 0, "right p upper .5")
    require(q(".528")*q(".18")+2*q(".22")*q(".0026")/ALPHA < q(".14"), "right h0")
    require(q(".14")**2 < q(".67")**2*q(".493"), "right h0 over sqrt p")
    require(DS*(1+(q(".125")-q(".0026")**2/ALPHA)/q(".5")) > q(".367"), "right K lower")
    require(DS*(1+q(".482")*(q(".75")-q(".482"))/q(".493")) < q(".4"), "right K upper")
    require(DS/q(".493") < q(".640") and DS*q(".75")/q(".493") < q(".48"), "right D,J upper")
    require(1+3*q(".482")-3*q(".528") > q(".8"), "right hstar lower")
    require(1+3*q(".5")-q("1.7")*q(".5") < q("1.77"), "right hstar upper")
    require(F(3, 10) < q(".475"), "right z lower")
    require((2*thi-q("3.87"))/(100*q(".97")) < q(".027"), "right chi upper")
    require(2*q(".88")-q(".027")/(1-q(".5")**2) > q(".68"), "right log M derivative")
    extra = q(".482")*(q(".75")-q(".482"))
    sub11 = ASTAR/4-MSTAR/2+MPRIME/4+q(".0026")**2/ALPHA+DS*(q(".5")+extra)**2/q(".5")
    sub22 = MPRIME+DS*(q("1.5")*q(".5"))**2/q(".493")
    require(sub11 < q(".403") and sub22 < q("1.12"), "right matrix diagonals")
    require(MPRIME/2+(-MSTAR+q("1.5")*q(".367"))*q(".5") > q(".080"), "right matrix offdiagonal lower")
    require(MPRIME/2+(-MSTAR+q("1.5")*q(".4"))*q(".482") < q(".13"), "right matrix offdiagonal upper")
    margin = (q(".43")-q(".403")-q(".022"))*(q("2.72")-q("1.12")-q(".75"))-q(".05")**2
    require(margin > 0, "right matrix determinant")
    print("Right-tail sufficient scalar/matrix margins: PASS")
    print("Right-tail determinant margin =", down(margin))


SECANTS = parse_rows("""
1.867 .52 1.314 2.34 .55 1.155
1.766 .49 1.813 2.564 .433 1.155
1.681 .664 2.057 2.621 .420 1.155
1.55 .847 2.101 2.461 .615 1.155
1.263 .912 1.787 1.885 .770 1.205
.913 .869 1.386 1.071 .840 1.251
""")


def secants():
    limits = [None, [q(".42")**2, q(".61")**2], [q(".20"), q(".295")],
              [q(".23")]*2, [q(".23")]*2, [q(".39")]*2]
    for ri, (name, row, triples) in enumerate(zip(("O", "P1", "R1", "U1", "V1", "T1"), BINS, SECANTS)):
        bmin, bmax, lmax, dmax, kmin, kmax, jmax, l1, _ = row
        bounds = []
        for zi, (zm, zM) in enumerate(((q("-.08"), q(".7")), (q("-.475"), F(0)))):
            claimed = triples[3*zi:3*zi+3]
            maxima = [F(0)]*3
            for b, l, k, j, h, z in product((bmin, bmax), (F(0), lmax), (kmin, kmax),
                                            (F(0), jmax), (q(".8"), q("1.77")), (zm, zM)):
                w = h-2*b-2*l*z
                vals = [abs(w), abs(ASTAR*b-MSTAR/2+l*z+k*w), abs(-MSTAR+j*w)]
                maxima = list(map(max, zip(maxima, vals)))
            require(all(x <= y for x, y in zip(maxima, claimed)), f"secant corners {name},{zi}")
            w, a, m = claimed
            chi = (q(".07"), q(".097"))[zi]
            cst = ASTAR+max(abs(zm), abs(zM))**2/ALPHA+a*a/l1+m*m/q(".75")
            if dmax is not None:
                bound = chi*chi*(cst+dmax*w*w)
                require(bound < limits[ri][zi], f"F_j bound {name},{zi}")
                bounds.append(up(bound))
            else:
                require(cst < (20, 12)[zi], "O constant term")
                require(q(".295")*w*w < (q("1.04"), q("1.63"))[zi], "O quadratic term")
                bounds.append(up(cst)+" + "+up(q(".295")*w*w)+" (7+t0^2)")
        quantity = "F_j/chi^2" if dmax is None else "F_j"
        print("Secant", name, quantity, "upper bounds:", "; ".join(bounds), "PASS")
    print("36 corner-derived constants and all 12 secant F_j bounds: PASS")


def main():
    print("Exact scalar certificate (standard-library Fraction arithmetic)")
    anchors()
    central()
    left_tail()
    right_tail()
    secants()
    print("ALL CHECKS PASSED. Decimal displays are outward rounded; all tests are rational.")


if __name__ == "__main__":
    main()
