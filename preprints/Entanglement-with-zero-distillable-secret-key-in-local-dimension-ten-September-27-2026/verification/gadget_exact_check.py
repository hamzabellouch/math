#!/usr/bin/env python3
"""Exact integer verification of the six measurement families.

All arithmetic is in Python integers.  Observables are integral real matrices;
R=4P is integral for each projection.  Thus tr(R_a R_b) is exactly 16 times
the overlap tr(P_a P_b).  The 4096 outcome assignments are exhaustively checked.
No numerical tolerance or external package is used.
"""
from itertools import product
import json


def eye(n):
    return tuple(tuple(int(i == j) for j in range(n)) for i in range(n))


def scale(c, a):
    return tuple(tuple(c*x for x in row) for row in a)


def add(a, b):
    return tuple(tuple(x+y for x, y in zip(ar, br)) for ar, br in zip(a, b))


def mul(a, b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(len(b)))
                       for j in range(len(b[0]))) for i in range(len(a)))


def kron(a, b):
    return tuple(tuple(a[i][j]*b[k][l] for j in range(len(a[0]))
                       for l in range(len(b[0]))) for i in range(len(a))
                 for k in range(len(b)))


def tr(a):
    return sum(a[i][i] for i in range(len(a)))


def transpose(a):
    return tuple(zip(*a))


I2, I4 = eye(2), eye(4)
X = ((0, 1), (1, 0))
Z = ((1, 0), (0, -1))
# Y=i J, so Y tensor Y = -(J tensor J).
J = ((0, -1), (1, 0))
array = ((kron(X, I2), kron(I2, X), kron(X, X)),
         (kron(I2, Z), kron(Z, I2), kron(Z, Z)),
         (kron(X, Z), kron(Z, X), scale(-1, kron(J, J))))
contexts = list(array) + [tuple(array[r][c] for r in range(3)) for c in range(3)]
signs = (1, 1, 1, 1, 1, -1)
outcomes = list(product((-1, 1), repeat=2))
projections_scaled_by_four = []
zero = scale(0, I4)
for a, s in zip(contexts, signs):
    for o in a:
        assert transpose(o) == o
        assert mul(o, o) == I4
    assert mul(a[0], a[1]) == mul(a[1], a[0])
    assert a[2] == scale(s, mul(a[0], a[1]))
    family = [mul(add(I4, scale(eps, a[0])), add(I4, scale(eta, a[1])))
              for eps, eta in outcomes]
    total = zero
    for alpha, R in enumerate(family):
        assert transpose(R) == R
        assert mul(R, R) == scale(4, R)
        assert tr(R) == 4
        eps, eta = outcomes[alpha]
        for o, eigenvalue in zip(a, (eps, eta, s*eps*eta)):
            assert mul(o, R) == scale(eigenvalue, R)
        total = add(total, R)
        for beta in range(alpha):
            assert mul(R, family[beta]) == zero
    assert total == scale(4, I4)
    projections_scaled_by_four.append(family)

overlaps_scaled_by_sixteen = [
    [[tr(mul(a, b)) for b in right]
     for a in left]
    for left in projections_scaled_by_four
    for right in projections_scaled_by_four
]
assert all(v >= 0 for block in overlaps_scaled_by_sixteen for row in block for v in row)
survivors = []
histogram = {}
for assignment in product(range(4), repeat=6):
    zero_pairs = sum(
        overlaps_scaled_by_sixteen[6*r+c][assignment[r]][assignment[c]] == 0
        for r in range(6) for c in range(r+1, 6)
    )
    histogram[str(zero_pairs)] = histogram.get(str(zero_pairs), 0)+1
    if zero_pairs == 0:
        survivors.append(assignment)
assert len(survivors) == 0

result = {
    'arithmetic': 'exact Python integers; R=4P and tr(RRprime)=16 tr(PPprime)',
    'context_names': ['row1', 'row2', 'row3', 'col1', 'col2', 'col3'],
    'context_signs': signs,
    'outcome_indices': outcomes,
    'observables': array,
    'projections_scaled_by_four': projections_scaled_by_four,
    'all_36_overlap_blocks_scaled_by_sixteen': overlaps_scaled_by_sixteen,
    'distinct_overlap_numerators_over_16': sorted({v for block in overlaps_scaled_by_sixteen for row in block for v in row}),
    'assignments_checked': 4**6,
    'assignments_with_all_pair_overlaps_positive': survivors,
    'histogram_number_of_zero_overlap_pairs': histogram,
    'all_assertions_passed': True,
}
print(json.dumps(result, indent=2))
