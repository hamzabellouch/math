#!/usr/bin/env python3
"""Independent unbounded opening audit from the standalone literal certificate.

The third reconstruction uses signed coordinate lookups and cellwise
membership. It imports neither of the other certificate checkers.
"""
import argparse
from pathlib import Path
import hashlib
import json
import re

class CertificateError(ValueError):
    """A literal or a proof obligation failed validation."""


def require(condition, message):
    """Validate identically with normal Python and python -O."""
    if not condition:
        raise CertificateError(message)


TABLE_SHA256 = '16d077f0b64df70dd67fb6e9651636d42eaab0ce0f01f46180a57846e38fedc2'
TARGET = {(0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1)}
O = (0, 0)
# A signed coordinate permutation is encoded as an output-coordinate lookup.
RECIPES = {
    'a': ((0, 1), (1, 1)), 'b': ((1, 1), (0, 1)),
    'c': ((0, 1), (1, -1)), 'd': ((1, -1), (0, 1)),
    'e': ((0, -1), (1, 1)), 'f': ((1, 1), (0, -1)),
    'g': ((0, -1), (1, -1)), 'h': ((1, -1), (0, -1)),
}
def linear(z, letter):
    return tuple(sign * z[axis] for axis, sign in RECIPES[letter])
def add(z, t):
    return z[0] + t[0], z[1] + t[1]
def sub(z, t):
    return z[0] - t[0], z[1] - t[1]
def place(zs, letter, translation):
    return {add(linear(z, letter), translation) for z in zs}


def template_records(templates):
    return [dict(row=i, a=sorted(a), h=sorted(h), height=rank)
            for i, (a, h, rank) in enumerate(templates)]


def templates_json(templates):
    return json.dumps(template_records(templates), sort_keys=True,
                      separators=(',', ':')).encode('ascii')


def reconstruct(raw):
    require(isinstance(raw, bytes), 'Certificate must be bytes')
    require(raw.endswith(b'\n'), 'Certificate must end with a newline')
    require(b'\r' not in raw, 'Certificate must use LF line endings')
    try:
        lines = raw.decode('ascii').split('\n')[:-1]
    except UnicodeDecodeError as exc:
        raise CertificateError('Certificate must contain only ASCII') from exc
    require(len(lines) == 610, f'Expected 610 rows, found {len(lines)}')
    req = [set(sub(z, s) for z in TARGET) - {O} for s in sorted(TARGET, key=lambda z: (z[1], z[0]))]
    env = [a | {O} for a in req]
    height = [1] * 6
    children = [[] for _ in range(6)]
    count = 0
    for i, line in enumerate(lines, 6):
        parts = line.split(' ')
        require(parts[0] == str(i) and len(parts) > 1,
                f'Expected row {i} followed by placements')
        parsed = []
        for term in parts[1:]:
            match = re.fullmatch(r'(0|[1-9][0-9]*)([a-h])([0-9])([0-9])', term)
            require(match is not None, f'Malformed placement token in row {i}: {term!r}')
            k = int(match[1]); letter = match[2]
            translation = (int(match[3]) - 4, int(match[4]) - 4)
            require(0 <= k < i, f'Row {i} contains a non-backward reference')
            parsed.append((k, letter, translation))
        cs = [place(req[k], letter, translation) for k, letter, translation in parsed]
        ds = [place(env[k], letter, translation) for k, letter, translation in parsed]
        # Derive requirements cellwise from membership, independently of verifier loop.
        universe = {O} | {z for d in ds for z in d} | {z for c in cs for z in c}
        new_req = {z for z in universe if z != O and (any(z in c for c in cs) or all(z in d for d in ds))}
        new_env = {z for z in universe if z == O or any(z in d for d in ds)}
        require(new_req < new_env, 'Validation failed: new_req < new_env')
        require(O in new_env - new_req, 'Validation failed: O in new_env - new_req')
        owned = new_req | {O}
        require(all(c <= owned for c in cs), 'Validation failed: all(c <= owned for c in cs)')
        for reply in new_env - owned:
            require(any(reply not in d for d in ds), 'Validation failed: any(reply not in d for d in ds)')
            count += 1
        # Every exterior reply misses every child envelope.
        require(all(d <= new_env for d in ds), 'Validation failed: all(d <= new_env for d in ds)')
        count += 1
        req.append(new_req); env.append(new_env)
        height.append(1 + max(height[k] for k, _, _ in parsed))
        children.append(parsed)
    require(len(req) == 616, 'Validation failed: len(req) == 616')
    placements = sum(map(len, children))
    require(placements == 1837, f'Expected 1837 placements, found {placements}')
    require(count == 26703, f'Expected 26703 local reply classes, found {count}')
    return req, env, height, children, count


def unbounded_opening(req, env):
    """Exact finite set identities covering every first reply in Z squared."""
    near_square = {(x, y) for x in (-1, 0, 1) for y in (-1, 0, 1)}
    far_envelopes = []
    far_records = []
    for row in (557, 595, 603):
        first = (-1, 0)
        for letter in RECIPES:
            shifted_required = {linear(sub(z, first), letter) for z in req[row]}
            shifted_envelope = {linear(sub(z, first), letter) for z in env[row]}
            require(shifted_required == {O}, f'Far opening {row}/{letter} does not require only origin')
            far_envelopes.append(shifted_envelope)
            far_records.append(dict(row=row, letter=letter,
                                    required=sorted(shifted_required),
                                    envelope_size=len(shifted_envelope),
                                    envelope_sha256=hashlib.sha256(json.dumps(
                                        sorted(shifted_envelope), separators=(',', ':')
                                    ).encode('ascii')).hexdigest()))
    require(len(far_envelopes) == 24, 'Expected exactly 24 far envelopes')
    common = set.intersection(*far_envelopes)
    require(common == near_square, 'The 24 far envelopes do not have the expected 3 by 3 intersection')
    # If an integer reply is outside this intersection, at least one entire
    # envelope avoids it. This implication quantifies over all lattice points;
    # no search radius or representative large integer is involved.
    near_records = []
    for first_reply in sorted(near_square - {O}):
        first = (1, 0) if 0 in first_reply else O
        local_reply = (1, -1)
        candidates = [letter for letter in RECIPES
                      if linear(sub(local_reply, first), letter) == first_reply]
        require(len(candidates) == 2, f'Expected two maps for near reply {first_reply}')
        placements = []
        for letter in candidates:
            def moved(z):
                return linear(sub(z, first), letter)
            domino = {moved(O), moved((1, 0))}
            second_candidates = domino - {O}
            require(len(second_candidates) == 1, 'Near opening must add exactly one Maker stone')
            second = next(iter(second_candidates))
            require(moved(first) == O and moved(local_reply) == first_reply,
                    'Near opening maps first Maker or Breaker stone incorrectly')
            require(second not in {O, first_reply}, 'Near opening second Maker stone is not legal')
            require({moved(z) for z in req[615] | {O}} == domino,
                    'Near opening does not own all row 615 requirements and pivot')
            require(first_reply not in {moved(z) for z in env[615]},
                    'Near opening row 615 envelope contains the first Breaker stone')
            placements.append(dict(letter=letter, second_maker=second))
        near_records.append(dict(first_breaker=first_reply, placements=placements))
    require(len(near_records) == 8, 'Expected eight nonzero near replies')
    return dict(
        unbounded_first_reply_cover=True,
        far_envelope_count=len(far_envelopes),
        far_envelope_common_intersection=sorted(common),
        far_envelopes=far_records,
        near_reply_count=len(near_records),
        near_placement_count=sum(len(item['placements']) for item in near_records),
        near_replies=near_records,
    )


def check(table, *, templates_path=None):
    raw = table.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == TABLE_SHA256, 'Table byte checksum mismatch')
    require(len(raw.splitlines()) == 610 and raw.endswith(b'\n'), "Validation failed: len(raw.splitlines()) == 610 and raw.endswith(b'\\n')")
    req, env, height, children, count = reconstruct(raw)
    templates = list(zip(req, env, height))
    expected_basis_images = {(u, v) for u in ((1, 0), (-1, 0), (0, 1), (0, -1))
                             for v in ((1, 0), (-1, 0), (0, 1), (0, -1))
                             if u[0] * v[0] + u[1] * v[1] == 0}
    require({(linear((1, 0), c), linear((0, 1), c)) for c in RECIPES}
            == expected_basis_images, 'Coordinate recipes must be all eight lattice symmetries')
    opening_proof = unbounded_opening(req, env)
    expected = {557: ({(-1, 0)}, 118, 19), 595: ({(-1, 0)}, 222, 27), 603: ({(-1, 0)}, 275, 27), 615: ({(1, 0)}, 686, 34)}
    for i, triple in expected.items():
        require((req[i], len(env[i]), height[i]) == triple, 'Validation failed: (req[i], len(env[i]), height[i]) == triple')
    require(max(height) == 34, 'Validation failed: max(height) == 34')
    require(sum(map(len, children)) == 1837 and count == 26703, 'Validation failed: sum(map(len, children)) == 1837 and count == 26703')
    require(not any(x <= -3 and y <= -2 for x, y in env[557]), 'Validation failed: not any(x <= -3 and y <= -2 for x, y in env[557])')
    require(not any(x == -2 and y <= -2 for x, y in env[595]), 'Validation failed: not any(x == -2 and y <= -2 for x, y in env[595])')
    require(not any(x <= -3 and y == 0 for x, y in env[603]), 'Validation failed: not any(x <= -3 and y == 0 for x, y in env[603])')
    require((1, -1) not in env[615], 'Validation failed: (1, -1) not in env[615]')

    # Focused tactical identities used in the explanatory examples.
    require(req[586] == {(0, -1), (0, -2)}, 'Validation failed: req[586] == {(0, -1), (0, -2)}')
    require(req[589] == {(-1, -t) for t in range(1, 5)}, 'Validation failed: req[589] == {(-1, -t) for t in range(1, 5)}')
    require(req[612] == {(-3, 0), (-2, 0), (-1, 0)}, 'Validation failed: req[612] == {(-3, 0), (-2, 0), (-1, 0)}')
    row612_envelopes = [place(env[k], letter, shift)
                        for k, letter, shift in children[612]]
    require(set.intersection(*row612_envelopes) == {(-t, 0) for t in range(4)}, 'Validation failed: set.intersection(*row612_envelopes) == {(-t, 0) for t in range(4)}')

    opening_counts = {557: 0, 595: 0, 603: 0, 'adjacent': 0, 'diagonal': 0}
    qs = {(x, y) for x in range(-50, 51) for y in range(-50, 51)} - {O}
    large = [0, 1, -1, 2, -2, 10**6, -10**6, 10**50, -10**50]
    qs |= {(x, y) for x in large for y in large} - {O}
    for q_star in qs:
        a, b = sorted(map(abs, q_star))
        require(b >= 1, 'Validation failed: b >= 1')
        if b >= 2:
            p = (-1, 0)
            i, d = (557, (-a, -b)) if a >= 2 else ((595, (-1, -b)) if a == 1 else (603, (-b, 0)))
            candidates = [letter for letter in RECIPES if linear(d, letter) == q_star]
            require(candidates, 'Validation failed: candidates')
            for letter in candidates:
                F = lambda z: linear(sub(z, p), letter)
                require(F(p) == O and F(add(p, d)) == q_star, 'Validation failed: F(p) == O and F(add(p, d)) == q_star')
                require({F(z) for z in req[i]} == {O}, 'Validation failed: {F(z) for z in req[i]} == {O}')
                require(q_star not in {F(z) for z in env[i]}, 'Validation failed: q_star not in {F(z) for z in env[i]}')
            opening_counts[i] += 1
        else:
            q = (1, -1); P = {O, (1, 0)}
            p = (1, 0) if a == 0 else O
            candidates = [letter for letter in RECIPES if linear(sub(q, p), letter) == q_star]
            require(candidates, 'Validation failed: candidates')
            for letter in candidates:
                F = lambda z: linear(sub(z, p), letter)
                require(F(p) == O and F(q) == q_star, 'Validation failed: F(p) == O and F(q) == q_star')
                m2, = {F(z) for z in P} - {O}
                require(m2 not in {O, q_star}, 'Validation failed: m2 not in {O, q_star}')
                require({O, m2} == {F(z) for z in req[615] | {O}}, 'Validation failed: {O, m2} == {F(z) for z in req[615] | {O}}')
                require(q_star not in {F(z) for z in env[615]}, 'Validation failed: q_star not in {F(z) for z in env[615]}')
            opening_counts['adjacent' if a == 0 else 'diagonal'] += 1

    P = {O, (1, 0)}
    row615_ds = [place(env[k], letter, shift) for k, letter, shift in children[615]]
    row615_cs = [place(req[k], letter, shift) for k, letter, shift in children[615]]
    require(set.intersection(*row615_ds) <= P, 'Validation failed: set.intersection(*row615_ds) <= P')
    require(all(c <= P for c in row615_cs), 'Validation failed: all(c <= P for c in row615_cs)')
    require(all((1, -1) not in d for d in row615_ds), 'Validation failed: all((1, -1) not in d for d in row615_ds)')
    nonbridge = [d for (k, _, _), d in zip(children[615], row615_ds) if k != 614]
    require(set.intersection(*nonbridge) == P | {(-1, 0)}, 'Validation failed: set.intersection(*nonbridge) == P | {(-1, 0)}')
    bridge, = [(k, letter, shift) for k, letter, shift in children[615] if k == 614]
    require(bridge == (614, 'b', (0, -1)), "Validation failed: bridge == (614, 'b', (0, -1))")
    require([k for (k, _, _), d in zip(children[615], row615_ds) if (-1, 0) not in d] == [614], 'Validation failed: [k for (k, _, _), d in zip(children[615], row615_ds) if (-1, 0) not in d] == [614]')
    bridge_pivot = add(linear(O, bridge[1]), bridge[2])
    require(bridge_pivot == (0, -1), 'Validation failed: bridge_pivot == (0, -1)')
    require(bridge_pivot not in P | {(1, -1), (-1, 0)}, 'Validation failed: bridge_pivot not in P | {(1, -1), (-1, 0)}')
    followup_pivots = {add(linear(shift, bridge[1]), bridge[2])
                       for _, _, shift in children[614]}
    require(followup_pivots == {(0, 1), (0, -2), (2, 0), (1, 2)}, 'Validation failed: followup_pivots == {(0, 1), (0, -2), (2, 0), (1, 2)}')

    reply_survivors = {}
    for reply in (env[615] - P) | {(10**50, 10**50)}:
        indices = [k for (k, _, _), d in zip(children[615], row615_ds) if reply not in d]
        require(indices, 'Validation failed: indices')
        require(max(height[k] for k in indices) <= 33, 'Validation failed: max(height[k] for k in indices) <= 33')
        reply_survivors[str(reply)] = indices

    result = {
        'status': 'PASS',
        'method': 'independent coordinate-lookup and cellwise-membership reconstruction',
        'table_sha256': hashlib.sha256(raw).hexdigest(),
        'all_templates_sha256': hashlib.sha256(templates_json(templates)).hexdigest(),
        'table_bytes': len(raw), 'data_rows': len(raw.splitlines()),
        'template_count': len(req), 'placement_count': sum(map(len, children)),
        'independent_local_reply_classes': count,
        'opening_points_checked': len(qs), 'opening_counts': {str(k): v for k, v in opening_counts.items()},
        'all_suitable_opening_matrices_checked': True,
        'large_integer_coordinates_include': str(10**50),
        'outputs': {i: {'required': sorted(req[i]), 'envelope_size': len(env[i]), 'height': height[i]} for i in expected},
        'row615_common_envelope': sorted(set.intersection(*row615_ds)),
        'row615_child_requirement_union': sorted(set.union(*row615_cs)),
        'row615_without614_common_envelope': sorted(set.intersection(*(d for (k, _, _), d in zip(children[615], row615_ds) if k != 614))),
        'row615_reply_minus1_0_survivors': [k for (k, _, _), d in zip(children[615], row615_ds) if (-1, 0) not in d],
        'row615_children': [{'child': k, 'letter': letter, 'shift': shift, 'height': height[k], 'required': sorted(c), 'pivot': add(linear(O, letter), shift)} for (k, letter, shift), c in zip(children[615], row615_cs)],
        'row615_all_child_requirements_owned_by_domino': True,
        'row615_all_child_envelopes_avoid_first_breaker': True,
        'row615_post_domino_reply_classes': len(reply_survivors),
        'tactical_required_sets': {i: sorted(req[i]) for i in (586, 589, 612)},
        'row612_common_envelope': sorted(set.intersection(*row612_envelopes)),
        'row615_exceptional_child_pivot': bridge_pivot,
        'placed_row614_followup_pivots': sorted(followup_pivots),
        'global_maker_move_bound': 35,
        'far_opening_maker_move_bound': 1 + max(height[k] for k in (557, 595, 603)),
        'post_domino_child_height_bound': max(height[k] for k, _, _ in children[615]),
        'opening_proof': opening_proof,
        'warning': 'Finite opening examples are supplemental; the exact 24-envelope intersection and eight near replies prove the unbounded opening.'
    }

    require(result['post_domino_child_height_bound'] == 33,
            'Post-domino Breaker-turn continuation must need at most 33 Maker moves')
    require(result['far_opening_maker_move_bound'] <= result['global_maker_move_bound'],
            'Every far opening must fit within the global Maker move bound')
    require(1 + 1 + result['post_domino_child_height_bound'] == result['global_maker_move_bound'],
            'The first stone, second domino stone, and child continuation must total 35 moves')
    if templates_path is not None:
        Path(templates_path).write_bytes(templates_json(templates) + b'\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', '--table', dest='table', type=Path,
                        default=Path(__file__).resolve().with_name('certificate.txt'))
    parser.add_argument('--json', type=Path, help='Also write the result to this path.')
    parser.add_argument('--templates-json', type=Path,
                        help='Write canonical required sets, envelopes and heights for all 616 templates.')
    args = parser.parse_args()
    result = check(args.table, templates_path=args.templates_json)
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.json:
        args.json.write_text(text)
    print(text, end='')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
