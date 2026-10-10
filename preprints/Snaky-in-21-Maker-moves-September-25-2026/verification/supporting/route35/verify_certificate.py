#!/usr/bin/env python3
"""Reconstruct the route-35 literal certificate using matrices and set operations.

Python 3.10+, standard library only. No data is executed and no search is run.
The mathematical induction interpreting these finite checks is in the article.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ORIGIN = (0, 0)
TARGET = ((0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1))
MATRICES = dict(zip("abcdefgh", (
    ((1, 0), (0, 1)), ((0, 1), (1, 0)),
    ((1, 0), (0, -1)), ((0, -1), (1, 0)),
    ((-1, 0), (0, 1)), ((0, 1), (-1, 0)),
    ((-1, 0), (0, -1)), ((0, -1), (-1, 0)),
)))
TABLE_SHA256 = "16d077f0b64df70dd67fb6e9651636d42eaab0ce0f01f46180a57846e38fedc2"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def placed(points, letter, shift):
    require(letter in MATRICES, "Unknown orientation")
    (a, b), (c, d) = MATRICES[letter]
    u, v = shift
    return frozenset((a*x + b*y + u, c*x + d*y + v) for x, y in points)


def parse(raw):
    """Validate structural completeness separately from byte identity."""
    require(isinstance(raw, bytes), "Expected certificate bytes")
    require(raw.endswith(b"\n"), "Missing final newline")
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise ValueError("Non-ASCII certificate") from exc
    # Split only LF; CR, tabs, blank lines, and alternate whitespace are invalid.
    lines = text[:-1].split("\n")
    require(len(lines) == 610, "Expected exactly 610 data rows")
    rows = []
    for expected, line in enumerate(lines, 6):
        require(re.fullmatch(r"[0-9]+(?: [0-9]+[a-h][0-9]{2})+", line)
                is not None, f"Malformed table row {expected}")
        fields = line.split(" ")
        require(fields[0] == str(expected), f"Wrong row index {expected}")
        terms = []
        for token in fields[1:]:
            match = re.fullmatch(r"(0|[1-9][0-9]*)([a-h])([0-9])([0-9])", token)
            require(match is not None, f"Malformed placement at row {expected}")
            child = int(match[1])
            require(0 <= child < expected, f"Nonbackward reference at row {expected}")
            terms.append((child, match[2], (int(match[3])-4, int(match[4])-4)))
        rows.append(terms)
    require(sum(map(len, rows)) == 1837, "Expected exactly 1837 placements")
    return rows


def template_records(templates):
    return [dict(row=i, a=sorted(a), h=sorted(h), height=rank)
            for i, (a, h, rank) in enumerate(templates)]


def template_digest(templates):
    return hashlib.sha256(json.dumps(template_records(templates), sort_keys=True,
                                    separators=(",", ":")).encode("ascii")).hexdigest()


def reconstruct(raw):
    rows = parse(raw)
    envelopes = [frozenset((x-u, y-v) for x, y in TARGET) for u, v in TARGET]
    required_sets = [h - {ORIGIN} for h in envelopes]
    heights = [1] * 6
    details = []
    reply_classes = 0
    for index, terms in enumerate(rows, 6):
        children_a, children_h, child_heights = [], [], []
        for child, letter, shift in terms:
            children_a.append(placed(required_sets[child], letter, shift))
            children_h.append(placed(envelopes[child], letter, shift))
            child_heights.append(heights[child])
        common = children_h[0]
        required_union = frozenset()
        envelope = frozenset({ORIGIN})
        for child_a, child_h in zip(children_a, children_h):
            common &= child_h
            required_union |= child_a
            envelope |= child_h
        required = (required_union | common) - {ORIGIN}
        height = 1 + max(child_heights)
        required_sets.append(required)
        envelopes.append(envelope)
        heights.append(height)
        owned = required | {ORIGIN}
        require(all(c <= owned for c in children_a), f"Unmet child requirement at {index}")
        require(all(d <= envelope for d in children_h), f"Escaping child envelope at {index}")
        # None represents all exterior points: every child lies in the envelope.
        for reply in (envelope - owned) | {None}:
            require(any(reply not in d for d in children_h), f"Uncovered reply at {index}")
            reply_classes += 1
        details.append(dict(row=index, terms=terms, common=sorted(common),
                            local_reply_classes=len(envelope - owned)+1))
    templates = list(zip(required_sets, envelopes, heights))
    require(len(templates) == 616, "Expected 616 templates")
    require(reply_classes == 26703, "Expected 26703 local reply classes")
    for i, (a, h, _) in enumerate(templates):
        require(a < h, f"Required set is not a proper envelope subset: {i}")
        require(ORIGIN in h and ORIGIN not in a, f"Invalid pivot: {i}")
    return templates, details, rows, reply_classes


def check_group():
    group = set(MATRICES.values())
    require(len(group) == 8, "Expected eight distinct matrices")
    for matrix in group:
        require(all(sum(abs(v) for v in row) == 1 for row in matrix), "Bad matrix row")
        for j in range(2):
            require(sum(abs(matrix[i][j]) for i in range(2)) == 1, "Bad matrix column")
        for other in group:
            product = tuple(tuple(sum(matrix[i][k]*other[k][j] for k in range(2))
                                  for j in range(2)) for i in range(2))
            require(product in group, "Matrices are not closed")


def tactical_checks(templates, rows):
    """Check the displayed chains, retaining both complete sets and old blockers."""
    def term_sets(term):
        child, letter, shift = term
        a, h, rank = templates[child]
        return placed(a, letter, shift), placed(h, letter, shift), rank

    row = lambda i: rows[i-6]
    require(row(589) == [(4, 'b', (0, -1)), (588, 'a', (0, 1))], "Wrong row 589 terms")
    require(row(588) == [(3, 'b', (-1, -1)), (586, 'a', (0, 1))], "Wrong row 588 terms")
    require(templates[589][0] == {(-1, -t) for t in range(1, 5)}, "Wrong four-column requirement")
    require(templates[586][0] == {(0, -1), (0, -2)}, "Wrong pair requirement")
    owned1 = templates[589][0] | {ORIGIN}
    threat1, continuation1 = [term_sets(t) for t in row(589)]
    require(threat1[1] == owned1 | {(0, -1)}, "First threat does not complete a target")
    require(continuation1[0] <= owned1, "Unowned 588 requirement")
    require(continuation1[1] <= templates[589][1], "588 envelope escapes 589")
    require((0, -1) not in continuation1[1], "588 contains first forced parry")
    owned2 = owned1 | {(0, 1)}
    local_threat2, local_continuation2 = [term_sets(t) for t in row(588)]
    threat2 = placed(local_threat2[1], 'a', (0, 1))
    continuation2_a = placed(local_continuation2[0], 'a', (0, 1))
    continuation2_h = placed(local_continuation2[1], 'a', (0, 1))
    require(len(threat2) == 6 and threat2 <= owned2 | {(-1, 0)}, "Second target completion fails")
    require((-1, 0) in threat2 and (-1, 0) not in owned2, "Wrong second threat cell")
    require(continuation2_a == {ORIGIN, (0, 1)}, "Wrong transferred pair")
    require(continuation2_a <= owned2, "Transferred pair not owned")
    require(continuation2_h == placed(templates[586][1], 'a', (0, 2)), "Wrong composite placement")
    require(continuation2_h <= continuation1[1] <= templates[589][1], "Transfer envelopes escape")
    require(not continuation2_h & {(0, -1), (-1, 0)}, "Transfer retains a forced blocker")
    require(row(612) == [(589, 'b', (1, 1)), (589, 'h', (-4, -1))], "Wrong opposite-tip placements")
    children612 = [term_sets(t) for t in row(612)]
    row_four = {(x, 0) for x in range(-3, 1)}
    require(templates[612][0] == row_four - {ORIGIN}, "Wrong row 612 requirement")
    require(children612[0][1] & children612[1][1] == row_four, "Wrong opposite-tip intersection")
    require(all(c <= row_four and d <= templates[612][1] for c,d,_ in children612), "Opposite-tip containment fails")

    domino = {ORIGIN, (1, 0)}
    first_breaker, exception = (1, -1), (-1, 0)
    children615 = [term_sets(t) for t in row(615)]
    require(all(c <= domino and d <= templates[615][1] and first_breaker not in d
                for c,d,_ in children615), "615 child containment or first-blocker failure")
    nonbridge = [d for (k,_,_),(_,d,_) in zip(row(615),children615) if k != 614]
    require(set.intersection(*(set(d) for d in nonbridge)) == domino | {exception}, "Wrong exceptional intersection")
    survivors = [t for t,(_,d,_) in zip(row(615),children615) if exception not in d]
    require(survivors == [(614, 'b', (0, -1))], "Wrong exceptional survivor")
    bridge_a, bridge_h, bridge_height = term_sets(survivors[0])
    pivot = (0, -1)
    require(pivot not in domino | {first_breaker, exception}, "Exceptional pivot is occupied")
    require(bridge_a <= domino and not bridge_h & {first_breaker, exception}, "Bridge not available")
    child614 = []
    for term in row(614):
        a,h,rank = term_sets(term)
        child614.append((placed(a,'b',pivot), placed(h,'b',pivot),rank))
    owned_bridge = domino | {pivot}
    require(all(c <= owned_bridge and d <= bridge_h for c,d,_ in child614), "Placed 614 children escape/need unowned cells")
    for reply in (bridge_h - owned_bridge) | {None}:
        require(any(reply not in d for _,d,_ in child614), "Placed 614 has uncovered reply")
    followup_pivots = {next(iter(placed({shift},'b',pivot))) for _,_,shift in row(614)}
    require(followup_pivots == {(0,1),(0,-2),(2,0),(1,2)}, "Wrong 614 continuation pivots")
    require(max(rank for _,_,rank in children615) == 33 and bridge_height == 33,
            "Wrong post-domino bound")
    return dict(status="PASS", transfer_chain=[589,588,586],
                forced_parries=[[0,-1],[-1,0]], transferred_pair=sorted(continuation2_a),
                transfer_shift=[0,2], transfer_envelopes_nested=True,
                transfer_envelope_avoids_both_parries=True,
                row612_common_envelope=sorted(row_four),
                row615_without614_common=sorted(domino | {exception}),
                exceptional_survivor=survivors[0], exceptional_pivot=pivot,
                placed614_followup_pivots=sorted(followup_pivots),
                all_tactical_child_requirements_owned=True,
                all_tactical_child_envelopes_contained=True,
                further_moves_after_second_breaker=33)


def check(table):
    raw = table.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    require(digest == TABLE_SHA256, "Table byte checksum mismatch")
    check_group()
    templates, details, rows, reply_classes = reconstruct(raw)
    outputs = (
        (557, (-1, 0), 118, 19, "x <= -3 and y <= -2", lambda x, y: x <= -3 and y <= -2),
        (595, (-1, 0), 222, 27, "x == -2 and y <= -2", lambda x, y: x == -2 and y <= -2),
        (603, (-1, 0), 275, 27, "x <= -3 and y == 0", lambda x, y: x <= -3 and y == 0),
        (615, (1, 0), 686, 34, "(x,y) == (1,-1)", lambda x, y: (x, y) == (1, -1)),
    )
    output_rows = []
    for i, point, size, rank, omitted_text, omitted in outputs:
        a, h, height = templates[i]
        require(a == {point}, f"Wrong required set at {i}")
        require(len(h) == size and height == rank, f"Wrong size/height at {i}")
        require(not any(omitted(x, y) for x, y in h), f"Claimed omitted region meets envelope {i}")
        output_rows.append(dict(row=i, a=sorted(a), h_size=len(h), height=height,
                                omitted_region=omitted_text, omitted=True))
    require(max(h for _, _, h in templates) == 34, "Wrong maximum height")
    require(templates[6][:2] == (frozenset((x-4, y-1) for x,y in TARGET)-{ORIGIN},
                               frozenset((x-4, y-1) for x,y in TARGET)), "Wrong elementary row 6")
    require(templates[7][0] == {(x, -1) for x in range(-4, 1)}, "Wrong elementary row 7")
    summary = dict(status="PASS", method="affine matrices and explicit set unions/intersections",
                   table_sha256=digest, table_bytes=len(raw), data_rows=len(rows),
                   templates=len(templates), placements=sum(map(len, rows)),
                   local_reply_classes=reply_classes, maximum_height=34,
                   signed_permutations=8, matrix_compositions=64,
                   all_templates_sha256=template_digest(templates), output_rows=output_rows,
                   tactics=tactical_checks(templates, rows))
    return summary, templates, details


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", "--table", dest="table", type=Path,
                        default=Path(__file__).resolve().with_name("certificate.txt"))
    parser.add_argument("--json", type=Path)
    parser.add_argument("--templates-json", type=Path)
    args = parser.parse_args()
    summary, templates, _ = check(args.table)
    text = json.dumps(summary, indent=2, sort_keys=True) + "\n"
    if args.json:
        args.json.write_text(text, encoding="ascii")
    if args.templates_json:
        args.templates_json.write_text(json.dumps(template_records(templates), sort_keys=True,
                                                 separators=(",", ":")) + "\n", encoding="ascii")
    print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
