#!/usr/bin/env python3
"""Replay the literal reduced-envelope 25-move certificate; Python 3 standard library.

This is finite set evaluation, not a strategy search or a Lean verification.
Every check uses an explicit exception and remains active with python -O/-OO.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

O = (0, 0)
S = ((0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1))
LITERAL_SHA = "41cd04620af889771862dcceda7383afd99933ae03ddb0a566a00d742a8249b0"
NUMERIC_SHA = "e0287ee160bcfc0451f796f73278bd82ad9cdee5704253b62c5803900c180f6c"
HISTOGRAM = [1, 5, 52, 217, 448, 523, 416, 219, 103, 30, 2]
EXPECTED_REDUCED_SHA = "db463db16ee7ffae7bb15b411623168e7e02cd7669bfbcc83982151585c43a1f"
EXPECTED_FULL_SHA = "458fe2d143a7772e21a28c3a468905676d87c5e0084c13ac209d2eae2d14a777"
EXPECTED_HEIGHTS_SHA = "1f3021c889abaac6b3b21efaf77456980d4396e9bec62799ef6b44263d18f5fa"


class CertificateError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise CertificateError(message)


def sha(value):
    return hashlib.sha256(value).hexdigest()


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode("ascii")


def rot(point, direction):
    x, y = point
    if direction & 1:
        x, y = y, x
    if direction & 2:
        x = -x
    if direction & 4:
        y = -y
    return x, y


def transport(points, anchor, direction):
    return {rot((x - anchor[0], y - anchor[1]), direction) for x, y in points}


def place(card, code):
    p, e, h = card
    k, direction = divmod(code, 8)
    require(0 <= k < len(p), "required-set anchor out of range")
    anchor = sorted(p)[k]
    return transport(p, anchor, direction), transport(e, anchor, direction), h


def attack(card, code):
    k, direction = divmod(code, 8)
    require(0 <= k < len(card[0]), "attack anchor out of range")
    anchor = sorted(card[0])[k]
    return rot((-anchor[0], -anchor[1]), direction)


def decode(line, current):
    require(re.fullmatch(r"[0-9]+", line) is not None and len(line) % 3 == 0,
            "row %d: expected nonempty ASCII decimal triples" % current)
    blocks = [int(line[n:n + 3]) for n in range(0, len(line), 3)]
    terms, cursor = [], 0
    while cursor < len(blocks):
        first = blocks[cursor]
        cursor += 1
        if first < 240:
            ref, code = divmod(first, 40)
        elif first < 740:
            distance, code = divmod(first - 240, 100)
            ref = current - 1 - distance
        else:
            require(cursor < len(blocks), "row %d: truncated extended term" % current)
            low, code = divmod(blocks[cursor], 100)
            cursor += 1
            ref = 10 * (first - 740) + low
        require(0 <= ref < current, "row %d: reference is not backward" % current)
        terms.append((ref, code))
    require(bool(terms), "empty composition")
    return terms


def reconstruct(raw, allow_noncanonical=False):
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise CertificateError("certificate must be ASCII") from exc
    cards = [({(x-a, y-b) for x, y in S if (x, y) != (a, b)}, {O}, 1)
             for a, b in S]
    full = [(p, p | e, h) for p, e, h in cards]
    rows, markers, terms_by_card = [], [], {}
    term_count, reply_classes = 0, 0
    decimal_cases = [0, 0, 0]
    for number, rawline in enumerate(text.splitlines(), 1):
        line = rawline.strip()
        if not line:
            continue
        current = len(cards)
        if line.startswith("#"):
            require(re.fullmatch(r"# [0-9]+", line) is not None,
                    "line %d: malformed marker" % number)
            marker = int(line[2:])
            require(marker == current, "line %d: marker/card mismatch" % number)
            markers.append(marker)
            continue
        require(current < 2016, "extra numeric row")
        terms = decode(line, current)
        terms_by_card[current] = terms
        rows.append(line)
        term_count += len(terms)
        cursor = 0
        while cursor < len(line):
            value = int(line[cursor:cursor+3])
            case = 0 if value < 240 else (1 if value < 740 else 2)
            decimal_cases[case] += 1
            cursor += 6 if case == 2 else 3
        children = [place(cards[j], r) for j, r in terms]
        up, ue, common = set(), set(), set(children[0][1])
        for p, e, h in children:
            up |= p
            ue |= e
            common &= e
        require(O in up, "row %d: anchor does not own pivot" % current)
        holdings = up | common
        parent_p = holdings - {O}
        parent_e = (ue - holdings) | {O}
        height = 1 + max(h for p, e, h in children)
        require(not parent_p & parent_e, "row %d: reduced sets overlap" % current)
        cards.append((parent_p, parent_e, height))

        # Evaluate the ordinary full-card rule on full children, without using
        # the computed reduced parent: A=(union A_j | intersection T_j)-{o};
        # T={o}|union T_j.  Verify the normalization bridge at every row.
        full_children = [place(full[j], r) for j, r in terms]
        required_union, envelope_union = set(), {O}
        envelope_common = set(full_children[0][1])
        for a, t, h in full_children:
            required_union |= a
            envelope_union |= t
            envelope_common &= t
        full_a = (required_union | envelope_common) - {O}
        full_h = 1 + max(h for a, t, h in full_children)
        require((full_a, envelope_union, full_h) ==
                (parent_p, parent_p | parent_e, height),
                "row %d: full/reduced normalization failed" % current)
        full.append((full_a, envelope_union, full_h))

        # These are all distinct local replies that can meet a child envelope,
        # plus one exterior class. Older Breaker cells are excluded by the
        # parent invariant; the conventional induction proves this for any M,B.
        replies = ue - holdings - {O}
        require(all(p <= (parent_p | {O}) for p, e, h in children),
                "row %d: child requirements not owned" % current)
        require(all(any(reply not in e for p, e, h in children) for reply in replies),
                "row %d: uncovered reply" % current)
        reply_classes += len(replies) + 1

    require(len(cards) == 2016 and len(rows) == 2010, "expected 2010 numeric rows / 2016 cards")
    require(markers == list(range(6, 2016, 50)), "expected all 41 ordered markers")
    require(term_count == 5862, "expected 5862 placement terms")
    numeric = ("\n".join(rows) + "\n").encode("ascii")
    if not allow_noncanonical:
        require(sha(raw) == LITERAL_SHA, "literal SHA256 mismatch")
        require(sha(numeric) == NUMERIC_SHA, "numeric-row SHA256 mismatch")
    require([len(cards), len(cards[-1][0]), len(cards[-1][1]), cards[-1][2]] ==
            [2016, 0, 389, 25], "wrong terminal card")
    histogram = [sum(len(p) == size for p, e, h in cards) for size in range(11)]
    require(histogram == HISTOGRAM, "required-set cardinality histogram mismatch")
    require(max(h for p, e, h in cards) == 25, "maximum height mismatch")
    examples = check_examples(cards, terms_by_card)
    reduced_json = [{"P": sorted(p), "E": sorted(e), "h": h} for p, e, h in cards]
    full_json = [{"A": sorted(a), "T": sorted(t), "h": h} for a, t, h in full]
    result = {
        "status": "PASS", "checker": "primary direct-set replay",
        "literal_data_sha256": sha(raw), "literal_data_bytes": len(raw),
        "numeric_rows_sha256": sha(numeric), "numeric_rows_bytes": len(numeric),
        "numeric_rows": len(rows), "cards": len(cards), "placement_terms": term_count,
        "marker_count": len(markers), "markers": markers,
        "decimal_case_counts": decimal_cases, "reply_classes": reply_classes,
        "endpoint": [2016, 0, 389, 25], "maximum_height": 25,
        "required_cardinality_histogram_0_to_10": histogram,
        "all_2010_composition_normalizations_exact": True,
        "reduced_sets_heights_sha256": sha(canonical(reduced_json)),
        "full_sets_heights_sha256": sha(canonical(full_json)),
        "heights_sha256": sha(canonical([h for p, e, h in cards])),
        **examples,
    }
    require(result["reduced_sets_heights_sha256"] == EXPECTED_REDUCED_SHA,
            "all-card reduced set/height digest mismatch")
    require(result["full_sets_heights_sha256"] == EXPECTED_FULL_SHA,
            "all-card full set/height digest mismatch")
    require(result["heights_sha256"] == EXPECTED_HEIGHTS_SHA, "height digest mismatch")
    return result, cards, terms_by_card, full


def check_examples(cards, terms_by_card):
    require(cards[6] == ({(-1, y) for y in range(-4, 1)}, {O, (0,-1), (0,1)}, 2),
            "elementary card 6 mismatch")
    require(cards[7] == ({(0,-4), (0,-3), (0,-2), (0,-1), (1,-4)},
                         {O, (1,-3), (1,-1), (1,0), (1,1)}, 3), "elementary card 7 mismatch")
    require(terms_by_card[6] == [(4,33),(5,33)] and terms_by_card[7] == [(4,5),(6,32)],
            "elementary decoder examples mismatch")
    require(attack(cards[4], 5) == (1,-3) and attack(cards[6], 32) == (1,0),
            "card 7 tactical pivots mismatch")
    cp, ce, ch = place(cards[6], 32)
    require(cp <= cards[7][0] | {O} and (1,-3) not in ce,
            "card 7 forced-block continuation mismatch")
    expected_required = {2014: {(1,0)}, 1874: {(-1,0)}, 1985: {(-1,0)},
                         1996: {(-1,0)}, 1998: {(0,1)}}
    for j, p in expected_required.items():
        require(cards[j][0] == p, "opening required set mismatch at %d" % j)
    common = set.intersection(*(place(cards[2014], d)[1] for d in range(8)))
    classes = {tuple(sorted(map(abs, p), reverse=True)) for p in common}
    require(classes == {(1,0),(1,1),(2,0),(2,1),(3,0)}, "opening exception classes mismatch")
    opening = []
    for reply, j, d, pivot in [((1,0),1874,2,(-1,0)), ((1,1),1985,6,(-1,0)),
                              ((2,0),1996,2,(-1,0)), ((2,1),1998,2,(0,-1)),
                              ((3,0),1996,2,(-1,0))]:
        p, e, h = place(cards[j], d)
        require(p == {O} and reply not in e and attack(cards[j],d) == pivot,
                "exception placement fails at %r" % (reply,))
        opening.append({"first_reply": reply, "row": j, "code": d,
                        "attack": pivot, "height": h, "envelope_size": len(e)})
    continuations = []
    outer_anchor = sorted(cards[1874][0])[0]
    for reply, j, r, pivot in [((-1,-1),1716,8,(-3,1)), ((-2,0),1752,3,(-1,2))]:
        require((j,r) in terms_by_card[1874], "missing advertised 1874 continuation")
        p, e, h = place(cards[j],r)
        p = transport(p, outer_anchor, 2)
        e = transport(e, outer_anchor, 2)
        actual = next(iter(transport({attack(cards[j],r)}, outer_anchor, 2)))
        require(p <= {O,(-1,0)} and not e & {(1,0),reply} and actual == pivot,
                "1874 continuation ownership or avoidance fails")
        require(actual not in {O,(-1,0),(1,0),reply}, "1874 continuation pivot is occupied")
        continuations.append({"reply": reply, "child": j, "code": r,
                              "inner_anchor": sorted(cards[j][0])[r//8],
                              "placed_required": sorted(p), "attack": actual,
                              "height": h, "avoids_old_and_new_replies": True})
    return {"example_cards_6_7": "PASS", "opening_common_cells": sorted(common),
            "opening_classes": sorted(classes), "opening": opening,
            "nonlocal_continuations": continuations,
            "card2014": {"required": sorted(cards[2014][0]),
                         "envelope_size": len(cards[2014][1]), "height": cards[2014][2]}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path,
                        default=Path(__file__).with_name("certificate.txt"))
    parser.add_argument("--json", action="store_true", help="print complete machine-readable result")
    parser.add_argument("--allow-noncanonical", action="store_true",
                        help="skip only literal/numeric byte identity checks (for negative tests)")
    args = parser.parse_args()
    try:
        result, cards, terms, full = reconstruct(args.certificate.read_bytes(), args.allow_noncanonical)
    except (OSError, CertificateError) as exc:
        print("FAIL: " + str(exc), file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps(result, sort_keys=True, indent=2))
    else:
        print("PASS route25: 2016 cards, 2010 rows, 5862 terms, 41 markers; endpoint (2016, 0, 389, 25)")
        print("Reduced sets/heights SHA256: " + result["reduced_sets_heights_sha256"])
        print("Full sets/heights SHA256: " + result["full_sets_heights_sha256"])
        print("Normalization, elementary cards, opening exceptions and both nonlocal continuations: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
