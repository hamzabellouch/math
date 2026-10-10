"""Optional finite-support, count, and 80-digit construction diagnostics.

This checks displayed numerical inequalities using high precision; it is not
an interval-arithmetic replacement for the submission's rational certificates.
Run from any directory with Python and mpmath 1.3.0. Run without -O.
Exact finite-support and count checks also occur in verify_construction.py,
which needs only the standard library. This script adds numerical diagnostics.
"""
from collections import Counter
from itertools import product
from pathlib import Path
import hashlib
import json
import mpmath as mp
if not __debug__:
    raise SystemExit('Run without -O: this checker uses assertions.')

mp.mp.dps = 80
M = mp.mpf
out = {'status': 'passed', 'arithmetic': '80-digit mpmath evaluation plus exact finite counts',
       'scope': 'Numerical diagnostics, not interval certificates for transcendental values.',
       'mpmath_version': mp.__version__, 'precision_decimal_digits': mp.mp.dps}

base3 = {'A': [(0, 0, 2), (0, 1, 1)],
         'B': [(2, 0, 0), (1, 1, 0)],
         'C': [(0, 2, 0)]}
six = [w for w in product(range(3), repeat=3) if sum(w) == 2]
weights = lambda w: (w[0] == 1) + (w[1] in (0, 2)) + (w[2] == 1)
retained = [w for w in six if weights(w) == 1]
assert sorted(retained) == sorted(sum(base3.values(), []))
assert weights((1, 0, 1)) == 3
for color, leaves in base3.items():
    for x, y, z in leaves:
        assert {'A': z > 0, 'B': x > 0, 'C': y == 2}[color]
        assert sum([z > 0, x > 0, y == 2]) == 1
out['boundary'] = {'six_terms': six, 'retained': retained,
                   'discarded_101_weight': weights((1, 0, 1))}

# Check the completion degeneration on the entire color alphabet.
for center in 'ABC':
    for m in (2, 3):
        noncenter = set('ABC') - {center}
        for word in product('ABC', repeat=m):
            weight = int(all(c == center for c in word))
            weight += sum(int(c in word) for c in noncenter)
            assert weight >= 1
            assert (weight == 1) == (len(set(word) & noncenter) <= 1)
out['completion_weight_checks'] = 'all 2- and 3-slot words for all centers pass'

# Enumerate the A-centered 3-slot tensor after retaining new colors B,C.
by_x = Counter()
branch_counts = Counter()
for word in product('ABC', repeat=3):
    if ('B' in word and 'C' in word) or set(word) == {'A'}:
        continue
    new_color = 'B' if 'B' in word else 'C'
    for leaves in product(*(base3[c] for c in word)):
        x = tuple(leaf[0] for leaf in leaves)
        by_x[x] += 1
        branch_counts[new_color] += 1
hist = Counter(by_x.values())
assert hist == {1: 8, 2: 12, 4: 6, 19: 1}
assert len(by_x) == 27 and sum(by_x.values()) == 75
assert branch_counts == {'B': 56, 'C': 19}
out['analytic_curve_support'] = {'fiber_histogram': {str(k): v for k,v in hist.items()},
                                 'branch_leaf_counts': dict(branch_counts)}
t = M(2) / 3
Z = sum(count * M(d)**t for d, count in hist.items())
g = sum(count * M(d)**t * mp.log(d) for d, count in hist.items()) / Z
h = mp.log(Z) - t*g
k = 2*g/h
cost = 6*mp.log(3)/h
out['analytic_curve_at_two_thirds'] = {key: str(value) for key, value in
    dict(Z=Z, g=g, h=h, k=k, cost=cost).items()}
assert k > M('.709') and cost < M('2.092')

# Direct full h-vector recursion (not the reduced D,delta recursion).
rho, b = M('.5'), 1
hs = {c: M(0) for c in 'ABC'}
rows = []
signed_script = [-2, 2, 2, -3, 2, -2, 3]
for step, signed_m in enumerate(signed_script, 1):
    m = abs(signed_m)
    old_rho, old_h, old_b = rho, dict(hs), b
    old_D = (rho*hs['B'] + (1-rho)*max(hs['A'], hs['C']))/b
    old_delta = abs(hs['A']-hs['C'])
    b *= m
    z = None
    if signed_m < 0:
        center = 'B'
        rho = old_rho**m
        hs['B'] = m*old_h['B']
        for c in 'AC':
            hs[c] = m*((old_rho-rho)*old_h['B'] + (1-old_rho)*old_h[c])/(1-rho)
        predicted_D = old_D
        predicted_delta = m*(1-old_rho)*old_delta/(1-rho)
    else:
        center = max('AC', key=lambda c: hs[c])
        other = 'C' if center == 'A' else 'A'
        rho = 1-(1-old_rho)**m
        hs['B'] = m*(old_rho*old_h['B']+(rho-old_rho)*old_h[center])/rho
        hs[center] = m*old_h[center]
        hs[other] = mp.log((mp.exp(old_h[center])+mp.exp(old_h[other]))**m
                           - mp.exp(m*old_h[center]))
        z = mp.log((1+mp.exp(-old_delta))**m-1)
        predicted_D = old_D + (1-rho)*max(0,z)/b
        predicted_delta = abs(z)
    D = (rho*hs['B']+(1-rho)*max(hs['A'],hs['C']))/b
    delta = abs(hs['A']-hs['C'])
    assert mp.almosteq(D,predicted_D,abs_eps=M('1e-70')) and mp.almosteq(delta,predicted_delta,abs_eps=M('1e-70')), (step,D,predicted_D,delta,predicted_delta)
    rows.append(dict(step=step, signed_m=signed_m, center=center, b=b,
                     rho=str(rho), delta=str(delta), D=str(D),
                     h={c:str(hs[c]) for c in 'ABC'}, z=None if z is None else str(z)))
out['seven_step_full_recurrence'] = rows
alpha = 2*D/mp.log(2)
out['dual_exponent'] = str(alpha)
assert alpha > M('.465')
third = rows[2]
assert mp.almosteq(M(third['rho']),1-M('.75')**4)
assert mp.almosteq(M(third['delta']),mp.log(M(9)/7))
assert mp.almosteq(M(third['D']),M('.5625')/4*mp.log(3))
assert M('.3194') < M(rows[3]['rho']) < M('.3195')
assert M('.348') < M(rows[3]['delta']) < M('.354')
assert 1-M(rows[4]['rho']) > M('.463')
assert M('.536') < M(rows[4]['rho']) < M('.537')
assert M('.635') < M(rows[4]['z']) < M('.651')
assert M(rows[5]['delta']) < M('.86')
assert 1-M(rows[6]['rho']) > M('.360')
assert M(rows[6]['z']) > M('.628')
loose_alpha = 2/M('.6932')*(M('.5625')*M('1.098')/4
               + M('.463')*M('.635')/48 + M('.360')*M('.628')/288)
out['displayed_loose_alpha_lower_bound'] = str(loose_alpha)
assert loose_alpha > M('.465')

# Exact integer square-certificate leaf counts, with no floating arithmetic.
counts = {'B':2,'A':2,'C':1}
count_rows = []
square_b = 1
for center, m in [('B',2),('A',3),('C',2),('B',2),('A',3)]:
    old = dict(counts)
    counts = {c:old[c]**m if c == center else (old[c]+old[center])**m-old[center]**m
              for c in old}
    square_b *= m
    count_rows.append(dict(center=center,m=m,b=square_b,counts=dict(counts)))
assert count_rows[2]['counts'] == {'B':20691584,'A':13993344,'C':10144225}
assert all(count_rows[3]['counts'][c] >= 10**12*factor
           for c,factor in [('B',428),('A',774),('C',522)])
N = counts['B']+counts['C']
bound_N = 10**36*(1202**3+1296**3-2*774**3)
assert N >= bound_N > 295*10**43
square_exponent = 3*square_b*mp.log(3)/mp.log(N)
out['square_count_rows'] = count_rows
out['square_certificate'] = dict(N=N, displayed_lower_bound=bound_N,
                                 exact_count_exponent=str(square_exponent),
                                 loose_N_exponent=str(216*mp.log(3)/mp.log(M('2.95e45'))))
assert square_exponent < M('2.267')

out['script_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
rendered = json.dumps(out, indent=2, sort_keys=True)+'\n'
Path(__file__).with_suffix('.json').write_text(rendered, encoding='utf-8')
print(rendered, end='')
