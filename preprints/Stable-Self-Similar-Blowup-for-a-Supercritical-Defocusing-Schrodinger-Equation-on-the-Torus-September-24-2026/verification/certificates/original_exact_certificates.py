#!/usr/bin/env python3
"""Independent exact finite arithmetic for the manuscript; standard library only.

Run: python -B checks/reviewer-B/exact_certificates.py > RESULTS.json
All pass/fail decisions use integers or Fraction. Diagnostic decimal values do not
participate in certification. Structural degree identities are mathematical
inputs, explained in the accompanying debate answer, not interval cancellations.
"""
from fractions import Fraction as F
from math import factorial, prod, sqrt
import json

H0, B, S = 10**8, 33477607, 270506819
ZERO = (0, 0, 0)


def p(r=0, i=0, e=0):
    return [(r, i, e)]


def add(a, b):
    out = []
    for j in range(max(len(a), len(b))):
        x = a[j] if j < len(a) else ZERO
        y = b[j] if j < len(b) else ZERO
        out.append(tuple(x[k] + y[k] for k in range(3)))
    return out


def neg(a):
    return [(-r, -i, e) for r, i, e in a]


def sub(a, b):
    return add(a, neg(b))


def mul(a, b):
    out = [ZERO] * (len(a) + len(b) - 1)
    for j, (r, i, e) in enumerate(a):
        for k, (s, t, f) in enumerate(b):
            u, v, w = out[j + k]
            out[j + k] = (
                u + r * s - i * t,
                v + r * t + i * s,
                w + e * (abs(s) + abs(t) + f) + (abs(r) + abs(i)) * f,
            )
    return out


def conjugate(a):
    return [(r, -i, e) for r, i, e in a]


def sharp(a):
    return [((-1)**j * r, -(-1)**j * i, e) for j, (r, i, e) in enumerate(a)]


def real(a):
    return [(r, 0, e) for r, i, e in a]


def imag(a):
    return [(i, 0, e) for r, i, e in a]


def hermitian_form(x, y, M, s, i, j):
    return add(mul(mul(M, conjugate(x[i])), x[j]),
               mul(s, sub(mul(conjugate(x[i]), y[j]),
                          mul(conjugate(y[i]), x[j]))))


def k8_boundary():
    rows = []
    cancelled = []
    for ell in range(4):
        M, s = p(H0 * (ell + 5)), p(0, S, 2)
        x, y = [p(1), p()], [p(), p(1)]
        for n in range(8):
            t = [(H0 * (ell + 2*n)//2 - H0//32, -B, 2), (0, H0, 0)]
            d = sub(t, M)
            x_new = [add(mul(t, xx), mul(s, yy)) for xx, yy in zip(x, y)]
            y = [sub(mul(d, yy), xx) for xx, yy in zip(x_new, y)]
            x = x_new
        A = hermitian_form(x, y, M, s, 0, 0)
        D = hermitian_form(x, y, M, s, 1, 1)
        C = hermitian_form(x, y, M, s, 0, 1)
        A, D, C = add(A, sharp(A)), add(D, sharp(D)), add(C, sharp(C))
        det = sub(mul(A, D), mul(C, conjugate(C)))
        cancellation = all(r == i == 0 for r, i, e in det[31:])
        assert cancellation
        cancelled.append(cancellation)
        coefficients = [[(det[2*j][0], 0, det[2*j][2])] for j in range(16)]
        row = []
        for U, V, J in [(0, 1, 1), (1, 10, 1), (10, 1, 0)]:
            q, m = p(), p(1)
            for j in range(15, -1, -1):
                q = add(mul(q, [(U, 0, 0), (V, 0, 0)]), mul(m, coefficients[j]))
                m = mul(m, [(1, 0, 0), (J, 0, 0)])
            row.append(min(r // (1 + e) for r, i, e in q[:16]))
        rows.append(row)
    expected = [[63, 60, 94], [21, 178, 199], [4, 13, 323], [1115, 173, 298]]
    assert rows == expected
    return {"interval_ratio_minima": rows, "central_high_degree_cancellations": cancelled,
            "structural_degree_bound_required": 30, "pass": True}


def separator_checks():
    separators = {0: [45,90,145,220,315,450,635,920,1780,3100],
                  1: [30,68,116,173,250,350,485,680,1005,1880,3210]}
    u = [51,78,94,121,165,218,278,369,490,720,1080,1930,3340]
    z = [6,17,28,36,40,47,55,62,69,64,68,90,181]
    rows = []
    for ell in range(4):
        x, y = p(), p(1)
        for n in range(7, -1, -1):
            t = [(H0 * (ell + 2*n)//2 - H0//32, -B, 0), (H0, 0, 0)]
            x, y = (add(mul(add(t, [(-H0*(ell+5), -S, 0)]), x), mul(p(0, -S), y)),
                    mul(t, add(x, y)))
        pp = [i for r, i, e in mul(x, conjugate(y))]
        assert len(pp) == 17 and pp[-1] == 0
        qs = [0] + (separators[ell] if ell < 2 else [a+(ell-2)*b for a,b in zip(u,z)]) + [7500]
        margins, signs, negative = [], [], []
        for positive, args in [(True, qs), (False, [50,200] if ell < 2 else [])]:
            for q in args:
                pair = []
                for c in (0, 1):
                    terms = [pp[2*j+c] * 100**(14-2*j) * ((-q*q) if positive else q*q)**j
                             for j in range(8)]
                    total = sum(terms)
                    pair.append('+' if total > 0 else '-')
                    margins.append(10**4 * abs(total) // sum(abs(t) for t in terms))
                (signs if positive else negative).append(''.join(pair))
        cycle = ['++', '-+', '--', '+-']
        start = [1, 0, 2, 2][ell]
        assert signs == [cycle[(start+j) % 4] for j in range(len(qs))]
        assert negative == (['++','--'] if ell < 2 else [])
        assert min(margins) == [583,432,80,68][ell]
        rows.append({"ell": ell, "q_over_100": qs, "positive_argument_signs": signs,
                     "negative_argument_signs": negative, "minimum_signed_margin": min(margins)})
    return {"rows": rows, "pass": True}


def k5_exterior():
    minima = []
    for zscale in [270400000, 300000000]:
        M, s = p(5*H0), [(0,zscale,0),(0,H0,0)]
        x, y = [p(1),p()], [p(),p(1)]
        for n in range(5):
            t = p(n*H0,-B,2)
            d = sub(t,M)
            x_new = [add(mul(t,xx),mul(s,yy)) for xx,yy in zip(x,y)]
            y = [sub(mul(d,yy),xx) for xx,yy in zip(x_new,y)]
            x = x_new
        d = hermitian_form(x,y,M,s,1,1)
        c = hermitian_form(x,y,M,s,1,0)
        margin = [(1130*H0**10*zscale,0,0),(1130*H0**11,0,0)]
        checks = ([real(d)[:11], add(mul(p(43),real(d)[:11]),
                                   mul(p(1000),sub(real(c)[:11],margin)))]
                  if zscale == 270400000 else [sub(neg(imag(c)[:9]),margin)])
        minima.extend(min(r//(1+e) for r,i,e in a) for a in checks)
    assert minima == [288247,17080,31628]
    b = F(335,1000)
    determinant_squared = prod((n*n+b*b)*((n-5)**2+b*b) for n in range(5))
    assert determinant_squared < 1130**2
    return {"interval_ratio_minima": minima, "determinant_bound_exact": True,
            "determinant_bound_diagnostic": sqrt(determinant_squared), "pass": True}


class C:
    """Exact rational complex scalar."""
    def __init__(self, r=0, i=0): self.r, self.i = F(r), F(i)
    def __add__(x,y): return C(x.r+y.r,x.i+y.i)
    def __sub__(x,y): return C(x.r-y.r,x.i-y.i)
    def __mul__(x,y): return C(x.r*y.r-x.i*y.i,x.r*y.i+x.i*y.r)
    def scale(x,t): return C(x.r*t,x.i*t)
    def n2(x): return x.r*x.r+x.i*x.i
    def div(x,y): return C((x.r*y.r+x.i*y.i)/y.n2(),(x.i*y.r-x.r*y.i)/y.n2())
    def a1(x): return abs(x.r)+abs(x.i)


def mm(A,B): return [[A[i][0]*B[0][j]+A[i][1]*B[1][j] for j in range(2)] for i in range(2)]
def ma(A,B): return [[A[i][j]+B[i][j] for j in range(2)] for i in range(2)]
def ms(A,s): return [[x.scale(s) for x in row] for row in A]
def ab(A): return [[C(x.a1()) for x in row] for row in A]
def zero(): return [[C(),C()],[C(),C()]]


def k34_profile():
    b,Z,delta = F('.33477606871236'),F('2.70506819293654'),F('1e-8')
    U,X,Y,E = [[C(1),C()],[C(),C(1)]],zero(),zero(),zero()
    G,H = [[C(0,-1),C()],[C(0,-1),C(0,-1)]],[[C(0,-1),C(0,-1)],[C(),C()]]
    N = ma(ab(G),ab(H))
    for n in range(33,-1,-1):
        t=C(n,-b); A=[[t-C(5,Z),C(0,-Z)],[t,t]]
        U,X,Y,E = (ms(mm(A,U),F(1,n+1)),
                   ms(ma(mm(G,U),mm(A,X)),F(1,n+1)),
                   ms(ma(mm(H,U),mm(A,Y)),F(1,n+1)),
                   ms(ma(mm(ma(ab(A),ms(N,delta)),E),mm(N,ma(ab(X),ab(Y)))),F(1,n+1)))
    m=U[0][1]
    checks={'m0_modulus':81<m.n2()<100}
    for label,v,lo,hi,li,ui in [
            ('U00_rectangle',U[0][0].div(m),'2.835','2.837','1.426','1.428'),
            ('X11_rectangle',X[1][1].div(m),'-.0811','-.0810','.1361','.1363'),
            ('Y11_rectangle',Y[1][1].div(m),'-.0001','.0001','.1237','.1240')]:
        checks[label]=F(lo)<v.r<F(hi) and F(li)<v.i<F(ui)
    checks['U11_ratio']=U[1][1].n2()<F('1e-24')*m.n2()
    checks['all_XY_ratios']=all(v.n2()<400*m.n2() for A in [X,Y] for row in A for v in row)
    checks['remainder_ratio']=all(v.n2()<50000**2*m.n2() for row in E for v in row)
    detsq=prod((n*n+(b+delta)**2)*((n-5)**2+(b+delta)**2) for n in range(34))/F(factorial(34)**4)
    checks['uniform_determinant_ratio']=detsq<F('6.2e-12')**2*m.n2()**2
    xc,yc=X[1][1].div(m),Y[1][1].div(m)
    lam=F('.048')**2; cross=xc.r*yc.r+xc.i*yc.i
    checks['minimum_stretch']=xc.n2()>lam and (xc.n2()-lam)*(yc.n2()-lam)>cross*cross
    a=U[0][0].div(m)
    checks['central_denominator_lower']= (C(1)-C(0,Z/F(5))*a).n2()>F('2.34')**2 and a.n2()<F('3.18')**2
    checks['linear_columns_for_j_bound']=xc.n2()<F('.159')**2 and yc.n2()<F('.124')**2
    # Explicit conservative propagation of the already certified bounds.
    change=40*delta+50000*delta**2
    den_variation=(1+(Z+delta)/5)*change+F('3.18')*delta/5
    right_variation=(Z+delta)*change/5+F('3.18')*delta/5
    checks['uniform_denominator_gap']=F('2.34')-F('3.18')*Z/5-den_variation-right_variation>F('.6')
    checks['L01_ratio_error']=change<F('5e-7')
    linear_size=F('.283')*delta
    jet_ratio_error=(F('1e-12')+50000*delta**2+linear_size*change)/(1-change)
    tail_ratio_error=(2*(Z+delta)/5)*F('6.2e-12')/(F('.6')*(1-change))
    total_error=jet_ratio_error+tail_ratio_error
    checks['j_linearization_error']=total_error<F('2.5e-11')
    checks['j_disk_bound']=linear_size+F('2.5e-11')<F('3e-9')
    checks['boundary_degree_margin']=F('.048')*delta>F('2.5e-11')
    checks['integer_error_box_contains_disk']=(abs(H0*b-B)+H0*delta<2 and abs(H0*Z-S)+H0*delta<2)
    assert all(checks.values()),checks
    diagnostics={'abs_m0':sqrt(m.n2()),'max_remainder_ratio':float(max(v.r for row in E for v in row))/sqrt(m.n2()),
                 'conservative_j_linearization_error':float(total_error)}
    return {'exact_comparison_checks':checks,'diagnostics_only':diagnostics,'pass':True}


def main():
    results={'arithmetic':'integer and exact rational; decimals marked diagnostic only',
             'k8_boundary':k8_boundary(),'separators':separator_checks(),
             'k5_exterior':k5_exterior(),'k34_profile':k34_profile()}
    print(json.dumps(results,sort_keys=True,indent=2))


if __name__=='__main__': main()
