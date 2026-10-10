#!/usr/bin/env python3
"""Independent review reconstruction: quarter turns and incidence masks.

This program reads a standalone literal certificate and reconstructs templates
using quarter turns, conjugation, and cell-incidence masks. It does not import
or execute either other checker. Detailed row output is optional.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import re

class CertificateError(ValueError):
    """A literal or a proof obligation failed validation."""


def require(condition, message):
    """Validate identically with normal Python and python -O."""
    if not condition:
        raise CertificateError(message)


TABLE_SHA256 = '16d077f0b64df70dd67fb6e9651636d42eaab0ce0f01f46180a57846e38fedc2'
ORIGIN = (0, 0)
S = ((0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1))
# Transform z by conjugating if requested and then multiplying by i^turns.
MAPS = dict(zip('abcdefgh', ((0, False), (1, True), (0, True),
                           (1, False), (2, True), (3, False),
                           (2, False), (3, True))))


def transform(p, code, shift=(0, 0)):
    x, y = p
    turns, conjugate = MAPS[code]
    if conjugate:
        y = -y
    for _ in range(turns):
        x, y = -y, x
    return x + shift[0], y + shift[1]


def parse_token(token):
    match = re.fullmatch(r'(0|[1-9][0-9]*)([a-h])([0-9])([0-9])', token)
    require(match is not None, f'Malformed placement token: {token!r}')
    prefix, letter, x, y = match.groups()
    return int(prefix), letter, (int(x) - 4, int(y) - 4)


def fingerprint(cells):
    return sha256(json.dumps(sorted(cells), separators=(',', ':')).encode()).hexdigest()


def template_records(templates):
    return [dict(row=i, a=sorted(a), h=sorted(h), height=rank)
            for i, (a, h, rank) in enumerate(templates)]


def templates_json(templates):
    """Canonical complete semantic output, including all six base templates."""
    return json.dumps(template_records(templates), sort_keys=True,
                      separators=(',', ':')).encode('ascii')


def reconstruct(data):
    require(isinstance(data, bytes), 'Certificate must be bytes')
    require(data.endswith(b'\n'), 'Certificate must end with a newline')
    require(b'\r' not in data, 'Certificate must use LF line endings')
    try:
        lines = data.decode('ascii').split('\n')[:-1]
    except UnicodeDecodeError as exc:
        raise CertificateError('Certificate must contain only ASCII') from exc
    require(len(lines) == 610, f'Expected 610 rows, found {len(lines)}')
    templates = []
    details = []
    for sx, sy in S:
        h = {(x-sx, y-sy) for x, y in S}
        templates.append((h - {ORIGIN}, h, 1))
    placements = 0
    total_classes = 0
    rectangle_classes = 0
    for index, line in enumerate(lines, 6):
        fields = line.split(' ')
        require(str(index) == fields[0] and len(fields) > 1,
                f'Expected row {index} followed by placements')
        terms = [parse_token(t) for t in fields[1:]]
        require(all(0 <= child < index for child, _, _ in terms),
                f'Row {index} contains a non-backward reference')
        placements += len(terms)
        incidences = {}
        child_required = []
        child_envelopes = []
        requirements = set()
        for j, (child, code, shift) in enumerate(terms):
            child_a, child_h, _ = templates[child]
            new_a = {transform(p, code, shift) for p in child_a}
            new_h = {transform(p, code, shift) for p in child_h}
            require(len(new_a) == len(child_a) and len(new_h) == len(child_h), 'Validation failed: len(new_a) == len(child_a) and len(new_h) == len(child_h)')
            child_required.append(new_a)
            child_envelopes.append(new_h)
            requirements.update(new_a)
            for p in new_h:
                incidences[p] = incidences.get(p, 0) | (1 << j)
        all_children = (1 << len(terms)) - 1
        common = {p for p, mask in incidences.items() if mask == all_children}
        a = (requirements | common) - {ORIGIN}
        h = set(incidences) | {ORIGIN}
        rank = max(templates[k][2] for k, _, _ in terms) + 1
        templates.append((a, h, rank))
        owned = a | {ORIGIN}
        require(a < h and ORIGIN not in a and ORIGIN in h, 'Validation failed: a < h and ORIGIN not in a and ORIGIN in h')
        require(all(c <= owned for c in child_required), 'Validation failed: all(c <= owned for c in child_required)')
        require(all(d <= h for d in child_envelopes), 'Validation failed: all(d <= h for d in child_envelopes)')
        # Each reply is represented by the subset of children it invalidates.
        # Points of h minus owned are exactly the possibly legal internal ones.
        histogram = Counter()
        survivor_witnesses = []
        for p in sorted(h - owned):
            mask = incidences.get(p, 0)
            survivors = [j for j in range(len(terms)) if not mask & (1 << j)]
            require(survivors, 'Validation failed: survivors')
            require(all(p not in child_envelopes[j] for j in survivors), 'Validation failed: all(p not in child_envelopes[j] for j in survivors)')
            histogram[len(survivors)] += 1
            survivor_witnesses.append((p, survivors[0]))
        # Independently test the bounding rectangle (including holes of h),
        # plus one explicit point beyond the rectangle. Any other external
        # reply has the same empty membership signature in every child.
        xs, ys = zip(*h)
        external = (max(xs)+1, max(ys)+1)
        require(all(external not in d for d in child_envelopes), 'Validation failed: all(external not in d for d in child_envelopes)')
        for x in range(min(xs), max(xs)+1):
            for y in range(min(ys), max(ys)+1):
                p = (x, y)
                if p not in owned:
                    require(any(p not in d for d in child_envelopes), 'Validation failed: any(p not in d for d in child_envelopes)')
                    rectangle_classes += 1
        rectangle_classes += 1
        classes = len(h - owned) + 1
        total_classes += classes
        details.append(dict(row=index, a=sorted(a), h=sorted(h), height=rank,
                            common=sorted(common), local_reply_classes=classes,
                            survivor_histogram=dict(histogram),
                            survivor_witnesses=survivor_witnesses,
                            a_sha256=fingerprint(a), h_sha256=fingerprint(h)))
    require(len(templates) == 616, 'Expected 616 reconstructed templates')
    require(placements == 1837, f'Expected 1837 placements, found {placements}')
    require(total_classes == 26703,
            f'Expected 26703 local reply classes, found {total_classes}')
    return templates, details, placements, total_classes, rectangle_classes


def check(table, *, templates_path=None):
    published = table.read_bytes()
    require(sha256(published).hexdigest() == TABLE_SHA256, 'Table byte checksum mismatch')
    require(len(published.splitlines()) == 610, 'Validation failed: len(published.splitlines()) == 610')
    require(published.endswith(b'\n'), "Validation failed: published.endswith(b'\\n')")
    # All map images are tested against the literal mathematical list, using
    # a point with distinct, nonzero coordinates to identify signed permutations.
    require([transform((2, 3), c) for c in MAPS] == [
        (2, 3), (3, 2), (2, -3), (-3, 2),
        (-2, 3), (3, -2), (-2, -3), (-3, -2)], 'Validation failed: [transform((2, 3), c) for c in MAPS] == [         (2, 3), (3, 2), (2, -3), (-3, 2),         (-2, 3), (3, -2), (-2, -3), (-3, -2)]')
    expected_basis_images = {(u, v) for u in [(1,0),(-1,0),(0,1),(0,-1)]
                             for v in [(1,0),(-1,0),(0,1),(0,-1)]
                             if u[0]*v[0]+u[1]*v[1] == 0}
    require({(transform((1, 0), c), transform((0, 1), c)) for c in MAPS} == expected_basis_images, 'Validation failed: {(transform((1, 0), c), transform((0, 1), c)) for c in MAPS} == expected_basis_images')

    templates, details, count_terms, count_replies, rectangle_checks = reconstruct(published)
    require(len(templates) == 616 and count_terms == 1837 and count_replies == 26703, 'Validation failed: len(templates) == 616 and count_terms == 1837 and count_replies == 26703')
    require(max(rank for _, _, rank in templates) == 34, 'Validation failed: max(rank for _, _, rank in templates) == 34')
    expected = {557: ((-1,0),118,19), 595: ((-1,0),222,27),
                603: ((-1,0),275,27), 615: ((1,0),686,34)}
    omitted = {
        557: lambda x,y: x <= -3 and y <= -2,
        595: lambda x,y: x == -2 and y <= -2,
        603: lambda x,y: x <= -3 and y == 0,
        615: lambda x,y: (x,y) == (1,-1),
    }
    summary_rows = []
    for row, (p, size, height) in expected.items():
        a, h, rank = templates[row]
        require(a == {p} and len(h) == size and rank == height, 'Validation failed: a == {p} and len(h) == size and rank == height')
        require(not any(omitted[row](*p) for p in h), 'Validation failed: not any(omitted[row](*p) for p in h)')
        summary_rows.append(dict(row=row, a=sorted(a), h_size=len(h), height=rank,
                                 h_sha256=fingerprint(h), omitted=True))
    require(templates[6][:2] == ({(x-4,y-1) for x,y in S}-{ORIGIN},
                                {(x-4,y-1) for x,y in S}), 'Validation failed: templates[6][:2] == ({(x-4,y-1) for x,y in S}-{ORIGIN},                                 {(x-4,y-1) for x,y in S})')
    require(templates[7][0] == {(x,-1) for x in range(-4,1)}, 'Validation failed: templates[7][0] == {(x,-1) for x in range(-4,1)}')

    summary = dict(method='independent quarter-turn/conjugation and incidence-bit-mask reconstruction',
                   table_sha256=sha256(published).hexdigest(),
                   all_templates_sha256=sha256(templates_json(templates)).hexdigest(),
                   table_bytes=len(published), data_rows=len(published.splitlines()),
                   status='PASS',
                   templates=len(templates), placements=count_terms,
                   local_reply_classes=count_replies, rectangle_reply_checks=rectangle_checks,
                   maximum_height=max(rank for _,_,rank in templates),
                   output_rows=summary_rows,
                   base_templates=[dict(row=i, a=sorted(a), h=sorted(h), height=rank)
                                   for i,(a,h,rank) in enumerate(templates[:6])],
                   example_rows=[details[0], details[1]])

    if templates_path is not None:
        Path(templates_path).write_bytes(templates_json(templates) + b'\n')
    return summary, details


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', '--table', dest='table', type=Path,
                        default=Path(__file__).resolve().with_name('certificate.txt'))
    parser.add_argument('--json', type=Path, help='Also write the summary to this path.')
    parser.add_argument('--rows-json', type=Path,
                        help='Optionally write every reconstructed nonbase row.')
    parser.add_argument('--templates-json', type=Path,
                        help='Write canonical required sets, envelopes and heights for all 616 templates.')
    args = parser.parse_args()
    summary, details = check(args.table, templates_path=args.templates_json)
    text = json.dumps(summary, indent=2) + '\n'
    if args.json:
        args.json.write_text(text)
    if args.rows_json:
        args.rows_json.write_text(json.dumps(details, indent=2) + '\n')
    print(text, end='')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
