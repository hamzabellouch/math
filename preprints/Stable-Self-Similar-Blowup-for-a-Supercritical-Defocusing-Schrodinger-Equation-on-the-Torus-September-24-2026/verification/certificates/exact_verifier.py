#!/usr/bin/env python3
"""Exact, dependency-free finite arithmetic accompanying the writeup.

Run from any working directory:
    python3 exact_verifier.py

Every pass/fail decision uses integers or fractions.Fraction. No floating-point
numbers are computed or emitted. Coefficients discarded by structural degree
or parity identities are mathematical inputs documented in README.md and in
this program's JSON output; central cancellation is only a consistency check.

Adapted from checks/reviewer-B/exact_certificates.py. The corresponding verifier
copy is original_exact_certificates.py; see ORIGINAL_SOURCE_SHA256 below.
"""
from fractions import Fraction as F
from hashlib import sha256
from math import factorial, prod
from pathlib import Path
import json

ORIGINAL_SOURCE_SHA256 = "51817ac46ec840887d1a70ab46482f04e662b7c1a0a497fdd0ea46924df32a7e"
H0, B, S = 10**8, 33477607, 270506819
ZERO = (0, 0, 0)


def require(condition, message):
    """Fail under ordinary Python and under python -O alike."""
    if not condition:
        raise ArithmeticError(message)


def rational(value):
    """Unambiguous exact JSON representation, with positive denominator."""
    value = F(value)
    return {"numerator": value.numerator, "denominator": value.denominator}



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
        require(all(i == 0 for r,i,e in det), "K8 central reality consistency check")
        require(all(r == i == 0 for r,i,e in det[1::2]), "K8 central parity consistency check")
        cancellation = all(r == i == 0 for r, i, e in det[31:])
        require(cancellation, "K8 central high-degree consistency check")
        cancelled.append(cancellation)
        coefficients = [[(det[2*j][0], 0, det[2*j][2])] for j in range(16)]
        row = []
        for U, V, J in [(0, 1, 1), (1, 10, 1), (10, 1, 0)]:
            q, m = p(), p(1)
            for j in range(15, -1, -1):
                q = add(mul(q, [(U, 0, 0), (V, 0, 0)]), mul(m, coefficients[j]))
                m = mul(m, [(1, 0, 0), (J, 0, 0)])
            require(all(x == ZERO for x in q[16:]), "K8 substitution discards zero padding only")
            require(all(i == 0 and r > e for r,i,e in q[:16]), "K8 positive coefficient intervals")
            row.append(min(r // (1 + e) for r, i, e in q[:16]))
        rows.append(row)
    expected = [[63, 60, 94], [21, 178, 199], [4, 13, 323], [1115, 173, 298]]
    require(rows == expected, "K8 interval ratio minima")
    return {"interval_ratio_minima": rows, "central_high_degree_consistency_checks": cancelled,
            "mathematical_inputs": [
                "Hermitian/reflection determinant is real and even for the entire coherent parameter family",
                "That determinant has degree at most 30 in v for the entire coherent parameter family"
            ],
            "central_cancellation_does_not_establish_degree_bound": True,
            "pass": True}


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
        require(len(pp) == 17 and pp[-1] == 0, "separator degree-16 coefficient vanishes")
        require(pp[15] == -8*S*H0**15, "separator leading coefficient")
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
        require(signs == [cycle[(start+j) % 4] for j in range(len(qs))], "separator positive signs")
        require(negative == (['++','--'] if ell < 2 else []), "separator negative signs")
        require(min(margins) == [583,432,80,68][ell], "separator exact signed margin")
        positive_changes = [sum(a[c] != b[c] for a,b in zip(signs, signs[1:])) for c in (0,1)]
        negative_order = list(reversed(negative)) + [signs[0]]
        negative_changes = [sum(a[c] != b[c] for a,b in zip(negative_order, negative_order[1:])) for c in (0,1)]
        require(positive_changes == [[5,6],[6,6],[7,7],[7,7]][ell], "positive root brackets")
        require([positive_changes[c]+negative_changes[c] for c in (0,1)] == [7,7], "root brackets exhaust both degree bounds")
        rows.append({"ell": ell, "q_over_100": qs, "positive_argument_signs": signs,
                     "positive_root_brackets_R_I": positive_changes,
                     "negative_root_brackets_R_I": negative_changes,
                     "exact_polynomial_degree": 15,
                     "negative_argument_signs": negative, "minimum_signed_margin": min(margins)})
    return {"rows": rows, "pass": True}


def k5_exterior():
    minima = []
    central_degree_checks = []
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
        degree_checks = {
            "real_d_above_degree_10": all(r == 0 for r,i,e in d[11:]),
            "c_above_degree_9": all(r == i == 0 for r,i,e in c[10:]),
            "imaginary_c_above_degree_8": all(i == 0 for r,i,e in c[9:]),
        }
        require(all(degree_checks.values()), "K5 central structural-degree consistency checks")
        central_degree_checks.append(degree_checks)
        margin = [(1130*H0**10*zscale,0,0),(1130*H0**11,0,0)]
        checks = ([real(d)[:11], add(mul(p(43),real(d)[:11]),
                                   mul(p(1000),sub(real(c)[:11],margin)))]
                  if zscale == 270400000 else [sub(neg(imag(c)[:9]),margin)])
        minima.extend(min(r//(1+e) for r,i,e in a) for a in checks)
    require(minima == [288247,17080,31628], "K5 interval ratio minima")
    b = F(335,1000)
    determinant_squared = prod((n*n+b*b)*((n-5)**2+b*b) for n in range(5))
    require(determinant_squared < 1130**2, "K5 determinant square bound")
    return {"interval_ratio_minima": minima, "determinant_bound_exact": True,
            "determinant_squared_upper_bound": rational(determinant_squared),
            "determinant_squared_comparison": 1130**2,
            "central_high_degree_consistency_checks": central_degree_checks,
            "mathematical_inputs": [
                "For the entire coherent parameter family, degree(d) <= 10 and degree(c) <= 9",
                "For the entire coherent parameter family, degree(Im(c)) <= 8"
            ],
            "central_cancellation_does_not_establish_degree_bound": True,
            "pass": True}


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
    require(all(checks.values()), "K34 comparison checks: " + repr(checks))
    return {'exact_comparison_checks':checks,
            'conservative_j_linearization_error': rational(total_error),
            'j_linearization_error_comparison': rational(F('2.5e-11')),
            'boundary_degree_margin_lower_bound': rational(F('.048')*delta-F('2.5e-11')),
            'uniform_denominator_gap_lower_bound': rational(F('2.34')-F('3.18')*Z/5-den_variation-right_variation),
            'pass':True}


def radd(*polynomials):
    """Sum real rational polynomials in ascending coefficient order."""
    result = [F(0)] * max(map(len, polynomials))
    for a in polynomials:
        for k, value in enumerate(a):
            result[k] += value
    return result


def rscale(a, scalar):
    return [scalar * x for x in a]


def rmul(*polynomials):
    """Multiply real rational polynomials in ascending coefficient order."""
    result = [F(1)]
    for a in polynomials:
        product = [F(0)] * (len(result) + len(a) - 1)
        for j, x in enumerate(result):
            for k, y in enumerate(a):
                product[j + k] += x * y
        result = product
    return result


def high_angular():
    """Check the straight-piece comparison and elementary path constants.

    Trigonometric monotonicity on [0, theta_0] and the path identities are
    analytic inputs. Every numerical comparison made from them is rational.
    """
    u0 = [F('.099'), F('.98')]
    umax = [F('.100'), F('.981')]
    vmax = [F('2.72'), F('.20')]
    L0 = [F('1.13'), F('.98')]
    q = [F(1), F('1.5')]
    d0 = radd(rmul(umax, umax), rmul(vmax, vmax))
    numerator_alpha_L = [F('-1.5'), F('2.75')]
    lower_bound = radd(
        rmul(radd([F(-3) - F(1, 32)], rscale(u0, F(1, 4))), L0, d0, q, q),
        rscale(rmul(u0, L0, q, q), F(81, 4)),
        rscale(rmul(L0, d0), F(5)),
        rscale(rmul(numerator_alpha_L, numerator_alpha_L, d0), F(-1)),
    )
    comparison = [F(2), F(33), F('-72.2'), F('44.8'), F('17.9'), F('-4.61'), F('.54')]
    difference = radd(lower_bound, rscale(comparison, F(-1)))
    require(len(difference) == 7 and all(x > 0 for x in difference),
            "all seven coefficients of the high-angular comparison difference are positive")
    discriminants = [F('-72.2')**2 - 4*F(33)*F('44.8'),
                     F('-4.61')**2 - 4*F('17.9')*F('.54')]
    require(discriminants == [F('-700.76'), F('-17.4119')], "high-angular quadratic discriminants")
    require(all(x < 0 for x in discriminants), "both comparison quadratics are positive")
    require(all(x > 0 for x in rmul(L0, d0, q, q)), "positive clearing denominator")

    Zstar, bstar, delta = F('2.70506819293654'), F('.33477606871236'), F('1e-8')
    Zmin, Zmax = Zstar-delta, Zstar+delta
    cosine, sine = F(99, 101), F(20, 101)
    cosine2, sine2 = cosine*cosine-sine*sine, 2*cosine*sine
    ujoin = sine/2
    vjoin_min, vjoin_max = Zmin+(1-cosine)/2, Zmax+(1-cosine)/2
    Ljoin_min = ujoin*cosine2 + vjoin_min*sine2
    Ljoin_max = ujoin*cosine2 + vjoin_max*sine2
    N_upper = F('.04') - F('2.70')*F('.92')
    Lprime_lower = F('.98') - 4*N_upper
    arc_potential_lower = -F(3)-F(1,32)+F('.3')*F('10.7')
    jump_lower = -F('1.5') - (F('.3')*F('1.19') + N_upper)
    boundary_lower = F(9,2)-Zmax
    geometry = {
        'unit_circle_identity': cosine*cosine+sine*sine == 1,
        'positive_sine_cosine': 0 < sine < 1 and 0 < cosine < 1,
        'cos_theta_above_point_98': cosine > F('.98'),
        'sin_2theta0_below_point_4': sine2 < F('.4'),
        'cos_2theta0_above_point_92': cosine2 > F('.92'),
        'arc_u_upper_bound': ujoin < F('.1'),
        'arc_v_lower_bound': Zmin > F('2.70'),
        'arc_v_upper_bound': vjoin_max < F('2.72'),
        'arc_N_upper_bound_negative': N_upper < 0,
        'arc_Lprime_above_10_point_7': Lprime_lower > F('10.7'),
        'arc_remaining_L_coefficient_positive': 3-F('.3')**2 > 0,
        'arc_potential_lower_bound_positive': arc_potential_lower > 0,
        'join_L_lower_bound': Ljoin_min > F('1.13'),
        'join_L_upper_bound': Ljoin_max < F('1.19'),
        'join_jump_lower_bound_positive': jump_lower > 0,
        'straight_u_intercept_bounds': F('.099') < ujoin < F('.100'),
        'straight_u_and_L_slope_bounds': F('.98') < cosine < F('.981'),
        'straight_v_slope_upper_bound': sine < F('.20'),
        'positive_lower_boundary_term_for_M_at_least_9': boundary_lower > 0,
        'profile_disk_above_exterior_threshold': Zmin > F('2.704'),
        'profile_b_positive_and_below_determinant_threshold': 0 < bstar-delta < bstar+delta < F('.335'),
    }
    require(all(geometry.values()), "high-angular rational geometry checks: " + repr(geometry))
    return {
        'coefficient_order': 'constant term first; indices 0 through 6',
        'lower_bound_coefficients': [rational(x) for x in lower_bound],
        'comparison_coefficients': [rational(x) for x in comparison],
        'difference_coefficients_all_strictly_positive': [rational(x) for x in difference],
        'quadratic_discriminants_both_strictly_negative': [rational(x) for x in discriminants],
        'exact_geometry_comparison_checks': geometry,
        'arc_potential_lower_bound': rational(arc_potential_lower),
        'join_jump_lower_bound': rational(jump_lower),
        'boundary_coefficient_lower_bound': rational(boundary_lower),
        'mathematical_inputs': [
            'The path identities and completing-square identity hold',
            'Sine and cosine have their elementary monotonicity on the indicated first-quadrant arc',
            'For t >= 0, the displayed geometric bounds yield the displayed lower-bound polynomial'
        ],
        'pass': True,
    }


def main():
    results = {
        'original_verifier_sha256': ORIGINAL_SOURCE_SHA256,
        'adapted_verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'arithmetic': 'integers and exact rational numbers only; no floating-point operations',
        'rational_encoding': '{"numerator": integer, "denominator": positive integer}',
        'scope': 'finite arithmetic, conditional on the explicitly listed mathematical inputs',
        'k8_boundary': k8_boundary(),
        'separators': separator_checks(),
        'k5_exterior': k5_exterior(),
        'k34_profile': k34_profile(),
        'high_angular': high_angular(),
    }
    require(all(results[name]['pass'] for name in
                ('k8_boundary', 'separators', 'k5_exterior', 'k34_profile', 'high_angular')),
            'all finite arithmetic checks must pass')
    results['all_finite_arithmetic_checks_pass'] = True
    print(json.dumps(results, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
