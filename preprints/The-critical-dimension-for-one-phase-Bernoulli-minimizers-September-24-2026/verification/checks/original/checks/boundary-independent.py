#!/usr/bin/env python3
"""Independent boundary certificate, using direct diagonal tensor components.

Uses only stdlib integer arithmetic; does not import/execute the submitted code.
All polynomial coefficients have denominator Q (S) or Q**2 (Lambda, E).
The supplied tables are data parsed literally from the hash-checked source.
"""
from collections import Counter, defaultdict
from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path

BASE = Path(__file__).resolve().parents[1]
SOURCE = BASE / "certificate-inputs.txt"
EXPECTED = "3b1e67b40af1740a1faab1ee8bbe85aa7c90dcb289fb5df2c8880de6956a8ffc"
Q = 250000
ZERO = (0, 0, 0, 0)
ONE = {ZERO: 1}


def clean(p):
    return {m: c for m, c in p.items() if c}


def add(*polys):
    result = defaultdict(int)
    for p in polys:
        for monomial, coeff in p.items():
            result[monomial] += coeff
    return clean(result)


def scale(p, c):
    return clean({m: c * a for m, a in p.items()})


def multiply(a, b):
    result = defaultdict(int)
    for ma, ca in a.items():
        for mb, cb in b.items():
            result[tuple(x + y for x, y in zip(ma, mb))] += ca * cb
    return clean(result)


def power(p, k):
    result = ONE
    for _ in range(k):
        result = multiply(result, p)
    return result


XS = [{tuple(int(i == j) for i in range(4)): 1} for j in range(4)]
SUM = add(*XS)
LAM = scale(SUM, -1)
EIG = [LAM] + XS
R = add(*(power(x, 2) for x in EIG))
TR3 = add(*(power(x, 3) for x in EIG))


def parse_tables(source):
    table_i = source.split("Table I:\n\n~~~\n", 1)[1].split("~~~", 1)[0]
    table_ii = source.split("Table II:\n\n~~~\n", 1)[1].split("~~~", 1)[0]
    rows = []
    for line in table_i.splitlines():
        kind, term, c = line.split()
        rows.append((kind, term, int(c)))
    boundary_blocks = []
    active = None
    for line in table_ii.splitlines():
        if line.startswith("@"):
            _, rank, projection, mode = line.split()
            active = None
            if int(rank) == -1:
                assert projection == "none" and mode in ("I", "H")
                active = {"mode": mode, "rows": []}
                boundary_blocks.append(active)
        elif active is not None:
            monomial, *coeffs = line.split()
            assert len(monomial) == 4 and sum(map(int, monomial)) <= 2
            active["rows"].append((tuple(map(int, monomial)), list(map(int, coeffs))))
    return rows, boundary_blocks, table_i, table_ii


@lru_cache(None)
def component(term, free_coords):
    """Evaluate an encoded tensor component at p=e_0, A=diag(lambda,x).

    Diagonal A**k has entries delta_ij eig[i]**k, including k=0.
    An endpoint 5 contracts with e_0 and therefore fixes that slot to 0.
    Free indices occur once, so no hidden free-index summations are needed.
    """
    digits = tuple(map(int, term))
    assert len(digits) % 3 == 0
    g_degree, cubic_degree, wz = digits[:3]
    assert wz == 0
    edges = list(zip(digits[3::3], digits[4::3], digits[5::3]))
    counts = Counter(i for a, b, _ in edges for i in (a, b))
    assert all(counts[i] == 1 for i in range(len(free_coords)))
    assert all(i == 5 or 0 <= i < len(free_coords) for i in counts)
    if g_degree:
        return {}
    answer = power(TR3, cubic_degree)
    for left, right, k in edges:
        i = 0 if left == 5 else free_coords[left]
        j = 0 if right == 5 else free_coords[right]
        if i != j:
            return {}
        answer = multiply(answer, power(EIG[i], k))
    return answer


def derive_s(rows):
    parts = {kind: {} for kind in "fUKM"}
    for kind, term, coeff in rows:
        if kind == "f":
            value = multiply(scale(LAM, -1), component(term, ()))
        elif kind == "M":
            value = component(term, (0,))
        elif kind == "P":
            assert int(term[0]) > 0
            continue
        elif kind == "U":
            value = component(term, (0, 0))
            for a in range(1, 5):
                sa = add(multiply(LAM, EIG[a]), scale(power(EIG[a], 2), -1))
                value = add(value, multiply(component(term, (a, a)), sa))
        elif kind == "K":
            value = {}
            for a in range(1, 5):
                sa = add(multiply(LAM, EIG[a]), scale(power(EIG[a], 2), -1))
                # C_0a0a + C_0aa0; C_00aa and C_0000 vanish identically.
                ck = add(component(term, (0, a, 0, a)),
                         scale(component(term, (a, 0, 0, a)), -1),
                         component(term, (0, a, a, 0)),
                         scale(component(term, (a, 0, a, 0)), -1))
                value = add(value, multiply(ck, sa))
        else:
            raise AssertionError(kind)
        parts[kind] = add(parts[kind], scale(value, coeff))
    return add(*parts.values()), parts


def derive_unaveraged_lambda(blocks):
    result = {}
    for block in blocks:
        rows = block["rows"]
        columns = len(rows[0][1])
        assert all(len(coeffs) == columns for _, coeffs in rows)
        for column in range(columns):
            j = add(*({monomial: coeffs[column]} for monomial, coeffs in rows))
            square = multiply(j, j)
            if block["mode"] == "H":
                square = multiply(square, SUM)
            result = add(result, square)
    return result


def homogenize(p):
    result = {}
    for monomial, coeff in p.items():
        degree = sum(monomial)
        assert degree <= 5
        result = add(result, multiply({monomial: coeff}, power(R, (5 - degree) // 2)))
    return result


def orbit_sum(p):
    result = defaultdict(int)
    for monomial, coeff in p.items():
        result[tuple(sorted(monomial))] += coeff
    return clean(result)


def permuted(p, permutation):
    return {tuple(m[i] for i in permutation): c for m, c in p.items()}


def serialized(p):
    return [{"exponents": list(m), "coefficient": c} for m, c in sorted(p.items())]


def main():
    raw = SOURCE.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    assert digest == EXPECTED
    source = raw.decode()
    rows, blocks, table_i, table_ii = parse_tables(source)
    s, parts = derive_s(rows)
    for permutation in itertools.permutations(range(4)):
        assert permuted(s, permutation) == s
    lam = derive_unaveraged_lambda(blocks)
    remainder = add(lam, {ZERO: Q * Q // 4}, scale(s, -Q))
    hom = homogenize(remainder)
    orbit = orbit_sum(hom)
    sum_abs = sum(abs(c) for c in orbit.values())
    # Independent averaging check: each sorted orbit coefficient represents
    # the average of a monomial over all 24 coordinate permutations.
    averaged_times_24 = add(*(permuted(hom, pi) for pi in itertools.permutations(range(4))))
    reconstructed_times_24 = {}
    for monomial, coeff in orbit.items():
        reconstructed_times_24 = add(reconstructed_times_24,
            *(permuted({monomial: coeff}, pi) for pi in itertools.permutations(range(4))))
    assert averaged_times_24 == reconstructed_times_24
    parity = {}
    for kind in ("U", "K"):
        counts = []
        for k, term, _ in rows:
            if k == kind:
                endpoints = term[3:]
                counts.append(sum(endpoints[i] == "5" for i in range(len(endpoints)) if i % 3 != 2))
        assert all(n % 2 == 0 for n in counts)
        parity[kind] = sorted(set(counts))
    result = {
        "input_sha256": digest,
        "implementation_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "table_i_sha256": hashlib.sha256(table_i.encode()).hexdigest(),
        "table_ii_sha256": hashlib.sha256(table_ii.encode()).hexdigest(),
        "implementation_dependencies": "Python 3 standard library only; no supplied code imported or executed",
        "table_i_counts": dict(Counter(kind for kind, _, _ in rows)),
        "boundary_block_shapes": [(b["mode"], len(b["rows"]), len(b["rows"][0][1])) for b in blocks],
        "even_p_endpoint_counts": parity,
        "Q": Q,
        "S_numerator_denominator_Q": serialized(s),
        "S_parts_numerators_denominator_Q": {k: serialized(p) for k, p in parts.items()},
        "homogenized_E_boundary_sorted_coefficients_denominator_Q_squared": serialized(orbit),
        "nonzero_sorted_keys": len(orbit),
        "Q_squared_times_sum_absolute_coefficients": sum_abs,
        "Q_squared_times_uniform_S_lower_bound": Q * Q // 4 - sum_abs,
        "claimed_key_count_matches": len(orbit) == 11,
        "claimed_sum_matches": sum_abs == 1656725282,
        "S_symmetric_verified_all_24_permutations": True,
        "averaging_verified_by_explicit_24_permutations": True,
    }
    target = BASE / "checks/boundary-independent-results.json"
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if not k.startswith("S_")}, indent=2))
    assert len(orbit) == 11 and sum_abs == 1656725282


if __name__ == "__main__":
    main()
