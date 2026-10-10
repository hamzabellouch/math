"""Small independent checks for thermal.py; never runs its production table.

The scalar model uses a full tensor-word basis and generic multiplication in
Z[w]/(w*w+w+1), rather than the packed code's phase-specific component formulas.
"""
from collections import deque
from fractions import Fraction
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
from itertools import product
from pathlib import Path
from random import Random
from struct import unpack as struct_unpack


HERE = Path(__file__).resolve().parent
BASE = 1 << 64
HALF = BASE // 2


def pack(digits, bits=64):
    return sum(value << (bits * lane) for lane, value in enumerate(digits))


def packed_floor(digits, bits=64, shift=4):
    # This is the source bit operation, parameterized for an exhaustive toy test.
    stride = sum(1 << (bits * lane) for lane in range(len(digits)))
    bias = (1 << (bits - 1)) * stride
    mask = ((1 << (bits - shift)) - 1) * stride
    return (((pack(digits, bits) + bias) >> shift) & mask) - (bias >> shift)


def check_floor_identity():
    count = 0
    # Exhaust all signed two-lane inputs of an 8-bit analogue, with division by 4.
    for digits in product(range(-128, 128), repeat=2):
        assert packed_floor(digits, 8, 2) == pack([x // 4 for x in digits], 8)
        count += 1
    edge = [-HALF, -HALF + 1, -HALF + 15, -HALF + 16,
            -17, -16, -15, -1, 0, 1, 15, 16, 17,
            HALF - 17, HALF - 16, HALF - 15, HALF - 2, HALF - 1]
    for digits in product(edge, repeat=3):
        assert packed_floor(digits) == pack([x // 16 for x in digits])
        count += 1
    rng = Random(20260915)
    for width in [1, 2, 3, 17, 191, 192]:
        for trial in range(50):
            digits = [rng.randrange(-HALF, HALF) for _ in range(width)]
            if trial % 2 == 0:
                digits[0] = -HALF
                digits[-1] = HALF - 1
            assert packed_floor(digits) == pack([x // 16 for x in digits])
            raw = (pack(digits) + HALF * sum(BASE**t for t in range(width)))
            unpacked = struct_unpack('<' + str(width) + 'Q', raw.to_bytes(8 * width, 'little'))
            assert tuple(x - HALF for x in unpacked) == tuple(digits)
            count += 1
    return count


def ring_mul(a, b):
    # (a0+a1*w)(b0+b1*w), reduced using w^2=-1-w.
    return (a[0]*b[0] - a[1]*b[1],
            a[0]*b[1] + a[1]*b[0] - a[1]*b[1])


def conjugate(a):
    return (a[0] - a[1], -a[1])


def scalar_matrix(n, twist):
    words = list(product((-1, 0, 1), repeat=n))
    positions = {word: i for i, word in enumerate(words)}
    rows = [[] for _ in words]
    for column, word in enumerate(words):
        diagonal = 16 - 3*n//2 - sum(word[j]*word[(j+1) % n] for j in range(n))
        rows[column].append((column, (diagonal, 0)))
        for site in range(n):
            neighbor = (site + 1) % n
            for step in (-1, 1):
                row_word = list(word)
                row_word[site] += step
                row_word[neighbor] -= step
                if any(abs(x) > 1 for x in row_word):
                    continue
                coefficient = (-1, 0)
                if neighbor == 0:
                    if twist == 1:
                        coefficient = (1, 0)
                    elif twist == 2:
                        # -w for y_0-x_0=+1; -w^-1=1+w for -1.
                        coefficient = (0, -1) if step == 1 else (1, 1)
                rows[positions[tuple(row_word)]].append((column, coefficient))
    entries = {(i, j): a for i, row in enumerate(rows) for j, a in row}
    assert all(entries[j, i] == conjugate(a) for (i, j), a in entries.items())
    return words, positions, rows


def word_orbits(words):
    unseen = {word for word in words if sum(word) >= 0}
    orbits = []
    while unseen:
        seed = min(unseen)
        orbit = {seed}
        pending = deque([seed])
        while pending:
            word = pending.popleft()
            for other in [word[1:] + word[:1], tuple(reversed(word))]:
                if other not in orbit:
                    orbit.add(other)
                    pending.append(other)
        unseen.difference_update(orbit)
        orbits.append((seed, len(orbit) * (1 if sum(seed) == 0 else 2)))
    assert sum(mult for _, mult in orbits) == len(words)
    return orbits


def scalar_columns(n, twist, probabilities):
    words, positions, matrix = scalar_matrix(n, twist)
    orbits = word_orbits(words)
    columns = {}
    total = 0
    max_coordinate = 0
    for representative, multiplicity in orbits:
        vector = [(0, 0)] * len(words)
        for probability in reversed(probabilities):
            next_vector = []
            for row in matrix:
                terms = [ring_mul(coefficient, vector[column]) for column, coefficient in row]
                pre_u, pre_v = (sum(term[k] for term in terms) for k in (0, 1))
                max_coordinate = max(max_coordinate, abs(pre_u), abs(pre_v))
                assert abs(pre_u) < HALF and abs(pre_v) < HALF
                next_vector.append((pre_u // 16, pre_v // 16))
            index = positions[representative]
            u, v = next_vector[index]
            next_vector[index] = (u + probability, v)
            vector = next_vector
        columns[representative] = vector
        total += multiplicity * sum(u*u - u*v + v*v for u, v in vector)
    expected_unpacks = []
    # Source iteration order is sectors 0..n, lexical rows, lexical representatives.
    for magnetization in range(n + 1):
        sector_words = [word for word in words if sum(word) == magnetization]
        reps = sorted(rep for rep in columns if sum(rep) == magnetization)
        assert 0 < len(reps) <= 192
        for word in sector_words:
            row = positions[word]
            for coordinate in (0, 1):
                expected_unpacks.append(tuple(columns[rep][row][coordinate] + HALF for rep in reps))
    return total, expected_unpacks, max_coordinate


def main():
    path = HERE / 'thermal.py'
    print('thermal_sha256', sha256(path.read_bytes()).hexdigest())
    print('floor_identity_cases', check_floor_identity())
    spec = spec_from_file_location('audited_thermal', path)
    source = module_from_spec(spec)
    spec.loader.exec_module(source)
    # Derive the coefficient sequence by exact rational recurrence.
    weights = [Fraction(1)]
    for j in range(1, 257):
        weights.append(weights[-1] * Fraction(84, j))
    denominator = sum(weights)
    probabilities = [int(source.Q * x / denominator) for x in weights]
    while probabilities[-1] == 0:
        probabilities.pop()
    assert probabilities == source.probs
    print('retained_coefficients', len(probabilities))
    for twist in range(3):
        scalar_total, expected_unpacks, max_coordinate = scalar_columns(4, twist, probabilities)
        actual_unpacks = []
        def capture_unpack(fmt, data):
            values = struct_unpack(fmt, data)
            actual_unpacks.append(values)
            return values
        source.unpack = capture_unpack
        packed_total = source.part(4, twist)
        assert actual_unpacks == expected_unpacks
        assert packed_total == scalar_total
        print('n=4 twist=', twist, 'total=', scalar_total,
              'unpack_calls=', len(actual_unpacks),
              'pre_floor_max=', max_coordinate)
    print('PASS: all exact scalar coordinates and totals agree with unchanged part().')


if __name__ == '__main__':
    main()
