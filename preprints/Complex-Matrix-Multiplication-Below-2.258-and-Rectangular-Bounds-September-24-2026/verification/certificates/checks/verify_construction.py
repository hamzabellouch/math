#!/usr/bin/env python3
"""Standard-library exact finite-support and monomial-count checks.

These small enumerations check the two completion sizes used in the paper,
the cubic curve's fiber histogram, and the five-step square witness. They
supplement the structural proof; they do not enumerate the optimization family.
Run without -O: assertions are the checks.
"""
from collections import Counter
from itertools import product
from pathlib import Path
import hashlib
import json

if not __debug__:
    raise SystemExit('Run without -O: this checker uses assertions.')

base = {'A': [(0, 0, 2), (0, 1, 1)],
        'B': [(2, 0, 0), (1, 1, 0)],
        'C': [(0, 2, 0)]}
six = [w for w in product(range(3), repeat=3) if sum(w) == 2]
def weight(w):
    return (w[0] == 1) + (w[1] in (0, 2)) + (w[2] == 1)
retained = [w for w in six if weight(w) == 1]
assert sorted(retained) == sorted(sum(base.values(), []))
assert weight((1, 0, 1)) == 3
for color, leaves in base.items():
    for x, y, z in leaves:
        assert {'A': z > 0, 'B': x > 0, 'C': y == 2}[color]
        assert sum([z > 0, x > 0, y == 2]) == 1

checked_words = 0
for center in 'ABC':
    for m in (2, 3):
        others = set('ABC') - {center}
        for word in product('ABC', repeat=m):
            monomial_weight = int(all(c == center for c in word))
            monomial_weight += sum(int(c in word) for c in others)
            assert monomial_weight >= 1
            assert (monomial_weight == 1) == (len(set(word) & others) <= 1)
            checked_words += 1

by_x, branch_counts = Counter(), Counter()
for word in product('ABC', repeat=3):
    if ('B' in word and 'C' in word) or set(word) == {'A'}:
        continue
    color = 'B' if 'B' in word else 'C'
    for leaves in product(*(base[c] for c in word)):
        by_x[tuple(leaf[0] for leaf in leaves)] += 1
        branch_counts[color] += 1
histogram = Counter(by_x.values())
assert histogram == {1: 8, 2: 12, 4: 6, 19: 1}
assert len(by_x) == 27 and sum(by_x.values()) == 75
assert branch_counts == {'B': 56, 'C': 19}

counts, b, rows = {'B': 2, 'A': 2, 'C': 1}, 1, []
for center, m in [('B', 2), ('A', 3), ('C', 2), ('B', 2), ('A', 3)]:
    old = counts.copy()
    counts = {c: old[c]**m if c == center else
              (old[c]+old[center])**m-old[center]**m for c in old}
    b *= m
    rows.append({'center': center, 'm': m, 'b': b, 'counts': counts.copy()})
assert rows[2]['counts'] == {'B': 20691584, 'A': 13993344, 'C': 10144225}
assert all(rows[3]['counts'][c] >= 10**12*factor
           for c, factor in [('B', 428), ('A', 774), ('C', 522)])
N = counts['B']+counts['C']
lower_N = 10**36*(1202**3+1296**3-2*774**3)
assert N == 2995461856366867388223311649574852466276480577
assert N >= lower_N > 295*10**43
assert b == 72

out = {'status': 'passed', 'arithmetic': 'integers and finite enumeration',
       'scope': 'Finite support, ownership flags, and monomial counts only.',
       'base_three_support': {'six_terms': six, 'retained': retained},
       'completion_words_checked': checked_words,
       'curve': {'fiber_histogram': {str(k): v for k, v in histogram.items()},
                 'leaves_by_branch': dict(branch_counts),
                 'number_of_x_words': len(by_x), 'number_of_leaves': sum(by_x.values())},
       'square': {'steps': rows, 'N': str(N), 'lower_N': str(lower_N)},
       'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
rendered = json.dumps(out, indent=2, sort_keys=True)+'\n'
Path(__file__).with_suffix('.json').write_text(rendered, encoding='utf-8')
print(rendered, end='')
