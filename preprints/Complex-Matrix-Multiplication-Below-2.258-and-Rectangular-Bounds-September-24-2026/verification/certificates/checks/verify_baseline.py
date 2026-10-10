#!/usr/bin/env python3
"""Exact checks for the specified published-table baseline and chord tests.

All inputs are local to this directory; all comparisons use Fraction.
This verifies arithmetic for a fixed dataset, not the source papers' proofs
or optimality of all untabulated algorithms. Run without -O.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json

if not __debug__:
    raise SystemExit('Run without -O: this checker uses assertions.')

data_path = Path(__file__).with_name('baseline_data.json')
data_bytes = data_path.read_bytes()
data = json.loads(data_bytes)
p, q = (F(data['separator'][key]) for key in ('p', 'q_star'))
v, u = (p-2)/(1-q), 1-q*(p-2)/(2*(1-q))
assert 0 < v < u < 1 and 2*u+v == p
assert (v, u) == (F(129, 275), F(9839, 11000))

def plane(k):
    k = F(k)
    return 2+v*(k-q) if k <= 1 else u*(1+k)+v

def record(z):
    return {'fraction': str(z), 'decimal_display': float(z)}

table_rows, flat_rows = [], []
for source in data['sources']:
    assert source['arxiv_version'] in source['url']
    for k_text, e_text in source['entries']:
        k, e = F(k_text), F(e_text)
        assert e >= max(2, 1+k)
        gap = e-plane(k)
        assert gap > 0, (source['id'], k_text, str(gap))
        groups = [group for group in data['grouped_roundings']
                  if F(group['k_min']) <= k <= F(group['k_max'])]
        if q < k:
            assert len(groups) == 1, (source['id'], k_text, groups)
            assert e >= F(groups[0]['e_min'])
        table_rows.append({'source': source['id'], 'k': k_text, 'e': e_text,
                           'plane': record(plane(k)), 'gap': record(gap)})
    if 'flat_endpoint' in source:
        alpha = F(source['flat_endpoint'])
        assert alpha < q
        flat_rows.append({'source': source['id'], 'k': str(alpha),
                          'e': '2', 'gap': record(2-plane(alpha))})

# Both versions are preserved separately, including their different square row.
old_rows = dict(data['sources'][1]['entries'])
new_rows = dict(data['sources'][2]['entries'])
assert old_rows.keys() == new_rows.keys()
assert all(old_rows[k] == new_rows[k] for k in old_rows if k != '1')
assert F(old_rows['1']) > F(new_rows['1']) > p

group_rows = []
for group in data['grouped_roundings']:
    lo, hi, e = (F(group[key]) for key in ('k_min', 'k_max', 'e_min'))
    # The plane is increasing on both sides of k=1, so the right endpoint
    # is the strongest check for the entire displayed group.
    gap = e-plane(hi)
    assert lo <= hi and gap > 0
    group_rows.append(dict(group, minimum_gap=record(gap)))
assert min(F(row['minimum_gap']['fraction']) for row in group_rows) == F(7, 22000)

ext = data['untabulated_extension']
available = {F(k): F(e) for k, e in ext['available_upper_estimates']}
assumed = {F(k): F(e) for k, e in ext['assumed_lower_envelope_constraints']}
for k, e in available.items():
    assert any(F(row['k']) == k and F(row['e']) <= e for row in table_rows)

chord_rows = []
for chord in ext['chord_extensions']:
    lo, hi = map(F, chord['interval'])
    near, lower = map(F, chord['near_lower'])
    far, upper = map(F, chord['far_upper'])
    assert assumed[near] == lower and available[far] == upper
    # The interval lies beyond the near endpoint, away from the far endpoint.
    # Convex extrapolation then has nonnegative coefficient on f(near)
    # and nonpositive coefficient on f(far), justifying lower/upper use.
    assert all((x-near)/(far-near) <= 0 for x in (lo, hi))
    slope = (upper-lower)/(far-near)
    intercept = lower-slope*near
    gaps = [intercept+slope*x-plane(x) for x in (lo, hi)]
    assert lo <= hi <= 1 and min(gaps) > 0
    chord_rows.append({'interval': chord['interval'],
                       'intercept': str(intercept), 'slope': str(slope),
                       'left_gap': record(gaps[0]), 'right_gap': record(gaps[1])})
assert min(F(row[key]['fraction']) for row in chord_rows
           for key in ('left_gap', 'right_gap')) == F(13, 22000)

def interpolate(x, left, right):
    x0, y0 = map(F, left)
    x1, y1 = map(F, right)
    assert x0 <= x <= x1
    return y0+(x-x0)*(y1-y0)/(x1-x0)

witness_rows = []
witnesses = data['new_witnesses']
for k_text in data['new_witness_plane_test_endpoints']:
    k = F(k_text)
    left, right = witnesses[:2] if k <= F(witnesses[1][0]) else witnesses[1:]
    bound = interpolate(k, left, right)
    gap = plane(k)-bound
    assert gap > 0
    witness_rows.append({'k': k_text, 'upper_witness_line': record(bound),
                         'plane': record(plane(k)), 'gap': record(gap)})
assert F(witness_rows[-1]['gap']['fraction']) == F(4159, 16005000)

# A second separator anchored at the recorded flat endpoint rules out an
# enlarged exponent-two region even after taking closure of the baseline.
# Here we instantiate the given square cost p=2.258; the paper treats p>2.
q0 = F(data['sources'][0]['flat_endpoint'])
flat_excess_rows = []
for row in table_rows:
    k, e = F(row['k']), F(row['e'])
    a0, b0, c0 = sorted((F(1), k, F(1)), reverse=True)
    excess, d = e-a0-b0, c0-q0*(a0+b0)/2
    assert excess >= 0
    if d > 0:
        assert excess > 0
        flat_excess_rows.append({'source': row['source'], 'k': row['k'],
                                 'size_excess': str(excess), 'd': str(d),
                                 'epsilon_upper_bound': str(excess/d)})
square_epsilon_bound = (p-2)/(1-q0)
assert square_epsilon_bound > 0 and flat_excess_rows
epsilon = min(F(1,2), square_epsilon_bound,
              *(F(row['epsilon_upper_bound']) for row in flat_excess_rows))
u0 = 1-q0*epsilon/2
assert 0 < epsilon <= F(1,2) and epsilon <= u0 <= 1
assert epsilon == F(46,4333)
for row in table_rows:
    k, e = F(row['k']), F(row['e'])
    a0, b0, c0 = sorted((F(1), k, F(1)), reverse=True)
    assert e >= u0*(a0+b0)+epsilon*c0
assert 2*u0+epsilon*q0 == 2 and 2*u0+epsilon <= p

# Check the full-range gap symbolically by matching affine coefficients in k,
# after factoring out (p-2). It is positive for p>2 and a<k<1.
a = F(witnesses[0][0])
factor = (a-q)/((1-q)*(1-a))
intercept = -q/(1-q)+a/(1-a)
slope = 1/(1-q)-1/(1-a)
assert q < a < 1 and factor == F(60, 1177)
assert intercept == factor and slope == -factor

out = {'status': 'passed', 'arithmetic': 'exact rational arithmetic',
       'scope': data['scope'], 'conditional_extension_scope': ext['scope'],
       'p': str(p), 'q_star': str(q), 'u': str(u), 'v': str(v),
       'automatic_size_bound_regimes': {'small_k_through': str(q),
                                       'large_k_from': str(2/q-1)},
       'table_entries_checked': len(table_rows), 'table_rows': table_rows,
       'flat_rows': flat_rows, 'grouped_rounding_rows': group_rows,
       'untabulated_chord_rows': chord_rows, 'new_witness_rows': witness_rows,
       'flat_endpoint_separator': {
           'scope': 'Finite input positivity and separator at the dataset square cost p=2.258.',
           'q0': str(q0), 'epsilon': record(epsilon), 'u0': str(u0),
           'square_epsilon_upper_bound': str(square_epsilon_bound),
           'positive_d_rows': flat_excess_rows,
           'normalized_plane': '2+epsilon*(k-q0), for q0 <= k <= 1',
           'all_finite_rows_and_square_pass': True},
       'full_range_gap': {'formula': '(p-2)*(1-k)*factor', 'factor': str(factor),
                          'conditions': '2 < p <= 2.258 and .465 < k < 1'},
       'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
       'data_sha256': hashlib.sha256(data_bytes).hexdigest()}
rendered = json.dumps(out, indent=2, sort_keys=True)+'\n'
Path(__file__).with_suffix('.json').write_text(rendered, encoding='utf-8')
print(rendered, end='')
