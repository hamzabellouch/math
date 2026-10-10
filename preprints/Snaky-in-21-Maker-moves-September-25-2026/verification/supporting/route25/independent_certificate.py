#!/usr/bin/env python3
"""Independent, standard-library-only reconstruction of the route-25 cards.

No other checker or supplied executable source is imported.  The full-envelope
recurrence and the disjoint reduced recurrence are evaluated separately.  Their
normalizations are compared at every composition, before checking the endpoint,
the opening cover, and the two advertised continuations.

The canonical reduced-card representation is an ASCII JSON list in card
order, with entries {"P": sorted coordinate pairs, "E": sorted coordinate
pairs, "h": height}; full cards instead use keys A,T,h. Keys are sorted,
separators are comma/colon, and one LF is appended. Heights use the same JSON
encoding of the ordered integer list. No check relies on Python assert.
"""

import argparse
from collections import namedtuple
import hashlib
import json
from pathlib import Path
import re
import sys


ORIGIN = (0, 0)
TARGET = ((0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1))
ROW_COUNT = 2010
CARD_COUNT = 2016
TERM_COUNT = 5862
MARKERS = tuple(range(6, 2007, 50))
RAW_SHA256 = "41cd04620af889771862dcceda7383afd99933ae03ddb0a566a00d742a8249b0"
NUMERIC_SHA256 = "e0287ee160bcfc0451f796f73278bd82ad9cdee5704253b62c5803900c180f6c"
REDUCED_SHA256 = "db463db16ee7ffae7bb15b411623168e7e02cd7669bfbcc83982151585c43a1f"
FULL_SHA256 = "458fe2d143a7772e21a28c3a468905676d87c5e0084c13ac209d2eae2d14a777"
HEIGHTS_SHA256 = "1f3021c889abaac6b3b21efaf77456980d4396e9bec62799ef6b44263d18f5fa"
EXPECTED_HISTOGRAM = (1, 5, 52, 217, 448, 523, 416, 219, 103, 30, 2)

# Row-major matrices, tabulated directly from the eight signed permutations.
ISOMETRIES = (
    (1, 0, 0, 1), (0, 1, 1, 0),
    (-1, 0, 0, 1), (0, -1, 1, 0),
    (1, 0, 0, -1), (0, 1, -1, 0),
    (-1, 0, 0, -1), (0, -1, -1, 0),
)
Card = namedtuple("Card", "required envelope height")


class InvalidCertificate(ValueError):
    """The input failed a stated certificate obligation."""


def demand(condition, message):
    if not condition:
        raise InvalidCertificate(message)


def digest(payload):
    return hashlib.sha256(payload).hexdigest()


def canonical_bytes(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode("ascii")


def read_rows(payload):
    """Parse ASCII triples and an exact, nonduplicated checkpoint schedule."""
    try:
        text = payload.decode("ascii")
    except UnicodeDecodeError as error:
        raise InvalidCertificate("certificate must contain only ASCII bytes") from error
    demand(text.endswith("\n"), "certificate must end with a newline")
    lines = text.split("\n")[:-1]
    if lines and lines[0] == "":
        lines.pop(0)
    rows = []
    numeric = []
    found_markers = []
    term_count = 0
    for line_number, line in enumerate(lines, 1):
        row_number = len(rows) + 6
        demand(bool(line), "unexpected blank line at input line %d" % line_number)
        if line.startswith("#"):
            demand(re.fullmatch(r"# (0|[1-9][0-9]{0,3})", line) is not None,
                   "malformed marker at input line %d" % line_number)
            marker = int(line[2:])
            demand(len(found_markers) < len(MARKERS), "too many markers")
            demand(marker == MARKERS[len(found_markers)],
                   "marker schedule mismatch at input line %d" % line_number)
            demand(marker == row_number, "marker does not identify the next card")
            found_markers.append(marker)
            continue
        demand(row_number < CARD_COUNT, "too many composition rows")
        if row_number in MARKERS:
            demand(found_markers and found_markers[-1] == row_number,
                   "missing marker before card %d" % row_number)
        demand(re.fullmatch(r"(?:[0-9]{3})+", line) is not None,
               "card %d is not a nonempty sequence of decimal triples" % row_number)
        words = tuple(int(line[offset:offset + 3]) for offset in range(0, len(line), 3))
        terms = []
        cursor = 0
        while cursor < len(words):
            head = words[cursor]
            cursor += 1
            if head < 240:
                reference = head // 40
                placement = head - 40 * reference
            elif head < 740:
                delta = head - 240
                reference = row_number - 1 - delta // 100
                placement = delta % 100
            else:
                demand(cursor < len(words), "truncated extended term in card %d" % row_number)
                tail = words[cursor]
                cursor += 1
                reference = (head - 740) * 10 + tail // 100
                placement = tail % 100
            demand(0 <= reference < row_number,
                   "non-backward reference %d in card %d" % (reference, row_number))
            terms.append((reference, placement))
        rows.append(tuple(terms))
        numeric.append(line)
        term_count += len(terms)
    demand(len(rows) == ROW_COUNT, "expected 2010 composition rows, got %d" % len(rows))
    demand(tuple(found_markers) == MARKERS, "incomplete marker schedule")
    demand(term_count == TERM_COUNT, "expected 5862 placement terms, got %d" % term_count)
    return tuple(rows), ("\n".join(numeric) + "\n").encode("ascii"), term_count


def image_point(point, anchor, matrix):
    x, y = point[0] - anchor[0], point[1] - anchor[1]
    a, b, c, d = matrix
    return (a * x + b * y, c * x + d * y)


def placement_parameters(card, code, label):
    anchor_number, orientation = divmod(code, 8)
    demand(0 <= anchor_number < len(card.required), "anchor out of range: " + label)
    return sorted(card.required)[anchor_number], ISOMETRIES[orientation]


def place(card, code, label):
    anchor, matrix = placement_parameters(card, code, label)
    required = frozenset(image_point(point, anchor, matrix) for point in card.required)
    envelope = frozenset(image_point(point, anchor, matrix) for point in card.envelope)
    demand(ORIGIN in required, "placement failed to align its anchor: " + label)
    return Card(required, envelope, card.height)


def attack(card, code, label):
    anchor, matrix = placement_parameters(card, code, label)
    return image_point(ORIGIN, anchor, matrix)


def serialize_cards(cards, full=False):
    required_key, envelope_key = ("A", "T") if full else ("P", "E")
    return canonical_bytes([
        {required_key: sorted(card.required), envelope_key: sorted(card.envelope), "h": card.height}
        for card in cards
    ])


def reconstruct(rows):
    """Construct full cards first; compare a separate reduced-set calculation."""
    demand(tuple(image_point((2, 3), ORIGIN, matrix) for matrix in ISOMETRIES) ==
           ((2, 3), (3, 2), (-2, 3), (-3, 2), (2, -3), (3, -2), (-2, -3), (-3, -2)),
           "signed-permutation convention mismatch")
    full = []
    reduced = []
    for hole in TARGET:
        translated = frozenset((point[0] - hole[0], point[1] - hole[1]) for point in TARGET)
        full.append(Card(translated.difference((ORIGIN,)), translated, 1))
        reduced_required = frozenset((x - hole[0], y - hole[1]) for x, y in TARGET if (x, y) != hole)
        reduced.append(Card(reduced_required, frozenset((ORIGIN,)), 1))

    for row_number, terms in enumerate(rows, 6):
        full_children = tuple(place(full[ref], code, "card %d, child %d" % (row_number, ref))
                              for ref, code in terms)
        full_union = frozenset().union(*(child.envelope for child in full_children))
        required_union = frozenset().union(*(child.required for child in full_children))
        common_full = full_children[0].envelope.intersection(*(child.envelope for child in full_children[1:]))
        next_full = Card((required_union | common_full).difference((ORIGIN,)),
                         full_union | frozenset((ORIGIN,)),
                         max(child.height for child in full_children) + 1)
        demand(next_full.required <= next_full.envelope, "full envelope omits holdings at card %d" % row_number)
        demand(ORIGIN not in next_full.required and ORIGIN in next_full.envelope,
               "full-card pivot invariant at card %d" % row_number)

        # Independently accumulate the reduced recurrence.  In particular its
        # intersections are on reduced E, not on the full envelopes above.
        reduced_children = [place(reduced[ref], code, "reduced card %d, child %d" % (row_number, ref))
                            for ref, code in terms]
        all_required, all_exclusions = set(), set()
        common_exclusions = set(reduced_children[0].envelope)
        reduced_height = 0
        for child in reduced_children:
            all_required.update(child.required)
            all_exclusions.update(child.envelope)
            common_exclusions.intersection_update(child.envelope)
            reduced_height = max(reduced_height, child.height)
        holdings = all_required | common_exclusions
        reduced_required = frozenset(holdings - {ORIGIN})
        reduced_exclusions = frozenset((all_exclusions - holdings) | {ORIGIN})
        next_reduced = Card(reduced_required, reduced_exclusions, reduced_height + 1)
        demand(not reduced_required.intersection(reduced_exclusions),
               "reduced sets overlap at card %d" % row_number)
        demand(next_full.required == reduced_required,
               "required-set normalization mismatch at card %d" % row_number)
        demand(next_full.envelope == reduced_required | reduced_exclusions,
               "envelope normalization mismatch at card %d" % row_number)
        demand(next_full.height == next_reduced.height,
               "height normalization mismatch at card %d" % row_number)
        full.append(next_full)
        reduced.append(next_reduced)
    return tuple(full), tuple(reduced)


def verify_examples(full, reduced, rows):
    expected_examples = (
        (6, frozenset((-1, y) for y in range(-4, 1)), frozenset(((0, 0), (0, -1), (0, 1)))),
        (7, frozenset(((0, -4), (0, -3), (0, -2), (0, -1), (1, -4))),
         frozenset(((0, 0), (1, -3), (1, -1), (1, 0), (1, 1)))),
    )
    for row, required, exclusions in expected_examples:
        demand(reduced[row].required == required and reduced[row].envelope == exclusions,
               "elementary reduced card %d mismatch" % row)
        demand(full[row].required == required and full[row].envelope == required | exclusions,
               "elementary full card %d mismatch" % row)
    demand(rows[0] == ((4, 33), (5, 33)) and rows[1] == ((4, 5), (6, 32)),
           "elementary card 6/7 terms mismatch")
    base_finish = place(reduced[4], 5, "elementary card 7 finish")
    following_fork = place(full[6], 32, "elementary card 7 fork")
    demand(base_finish.envelope == frozenset(((1, -3),)), "elementary card 7 blocking hole mismatch")
    demand(attack(full[6], 32, "elementary card 7 fork") == (1, 0)
           and (1, -3) not in following_fork.envelope,
           "elementary card 7 continuation mismatch")

    demand(full[2014].required == frozenset(((1, 0),)), "card 2014 singleton mismatch")
    for row, point in ((1874, (-1, 0)), (1985, (-1, 0)), (1996, (-1, 0)), (1998, (0, 1))):
        demand(full[row].required == frozenset((point,)), "opening singleton mismatch at card %d" % row)
    opening_images = [place(full[2014], orientation, "opening cover") for orientation in range(8)]
    common = opening_images[0].envelope.intersection(*(card.envelope for card in opening_images[1:])) - {ORIGIN}
    exceptional_classes = ((1, 0), (1, 1), (2, 0), (2, 1), (3, 0))
    expected_common = frozenset(image_point(point, ORIGIN, matrix)
                                for point in exceptional_classes for matrix in ISOMETRIES)
    demand(common == expected_common, "opening exceptional orbit cover mismatch")
    opening = []
    for reply, row, code, expected_attack in (
            ((1, 0), 1874, 2, (-1, 0)), ((1, 1), 1985, 6, (-1, 0)),
            ((2, 0), 1996, 2, (-1, 0)), ((2, 1), 1998, 2, (0, -1)),
            ((3, 0), 1996, 2, (-1, 0))):
        placed = place(full[row], code, "exceptional opening")
        next_attack = attack(full[row], code, "exceptional opening")
        demand(placed.required == frozenset((ORIGIN,)) and reply not in placed.envelope,
               "opening placement is unavailable for %r" % (reply,))
        demand(next_attack == expected_attack and next_attack not in (ORIGIN, reply),
               "opening attack mismatch or occupied attack for %r" % (reply,))
        opening.append({"first_reply": reply, "row": row, "code": code,
                        "attack": next_attack, "height": full[row].height})

    outer_anchor, outer_matrix = placement_parameters(full[1874], 2, "card 1874 outer placement")
    maker_stones = frozenset((ORIGIN, (-1, 0)))
    continuations = []
    for reply, child, code, expected_attack in (
            ((-1, -1), 1716, 8, (-3, 1)), ((-2, 0), 1752, 3, (-1, 2))):
        demand((child, code) in rows[1874 - 6], "advertised continuation absent from card 1874")
        placed = place(full[child], code, "card 1874 continuation")
        actual_required = frozenset(image_point(p, outer_anchor, outer_matrix) for p in placed.required)
        actual_envelope = frozenset(image_point(p, outer_anchor, outer_matrix) for p in placed.envelope)
        inner_attack = attack(full[child], code, "card 1874 continuation")
        actual_attack = image_point(inner_attack, outer_anchor, outer_matrix)
        breaker_stones = frozenset(((1, 0), reply))
        demand(actual_required <= maker_stones, "continuation needs an unowned Maker cell")
        demand(not actual_envelope.intersection(breaker_stones), "continuation envelope contains an old Breaker cell")
        demand(actual_attack == expected_attack and actual_attack not in maker_stones | breaker_stones,
               "continuation attack mismatch or occupied attack")
        continuations.append({"reply": reply, "child": child, "code": code, "attack": actual_attack})
    return sorted(common), list(exceptional_classes), opening, continuations


def verify(path, allow_noncanonical=False):
    payload = Path(path).read_bytes()
    rows, numeric, term_count = read_rows(payload)
    raw_hash, numeric_hash = digest(payload), digest(numeric)
    if not allow_noncanonical:
        demand(raw_hash == RAW_SHA256, "raw certificate SHA-256 mismatch")
        demand(numeric_hash == NUMERIC_SHA256, "numeric rows SHA-256 mismatch")
    full, reduced = reconstruct(rows)
    endpoint = [len(full), len(full[-1].required), len(full[-1].envelope), full[-1].height]
    demand(endpoint == [2016, 0, 389, 25], "terminal card endpoint mismatch: %r" % endpoint)
    histogram = [sum(len(card.required) == size for card in full) for size in range(11)]
    demand(histogram == list(EXPECTED_HISTOGRAM), "required-cardinality histogram mismatch")
    demand(sum(histogram) == CARD_COUNT, "required set outside histogram range")
    heights = [card.height for card in full]
    demand(max(heights) == 25, "maximum height mismatch")
    common, classes, opening, continuations = verify_examples(full, reduced, rows)
    full_bytes, reduced_bytes = serialize_cards(full, full=True), serialize_cards(reduced)
    full_hash = digest(full_bytes)
    reduced_hash = digest(reduced_bytes)
    heights_hash = digest(canonical_bytes(heights))
    demand(full_hash == FULL_SHA256, "full sets/heights SHA-256 mismatch")
    demand(reduced_hash == REDUCED_SHA256, "reduced sets/heights SHA-256 mismatch")
    demand(heights_hash == HEIGHTS_SHA256, "heights SHA-256 mismatch")
    return {
        "status": "PASS", "checker": "independent_certificate",
        "literal_data_sha256": raw_hash, "literal_data_bytes": len(payload),
        "numeric_rows_sha256": numeric_hash, "numeric_rows_bytes": len(numeric),
        "numeric_rows": len(rows), "cards": len(full), "placement_terms": term_count,
        "marker_count": len(MARKERS), "endpoint": endpoint, "maximum_height": max(heights),
        "required_cardinality_histogram_0_to_10": histogram,
        "full_sets_heights_sha256": full_hash, "reduced_sets_heights_sha256": reduced_hash,
        "heights_sha256": heights_hash,
        "all_2010_composition_normalizations_exact": True,
        "opening_common_cells": common, "opening_classes": classes,
        "opening": opening, "nonlocal_continuations": continuations,
        "example_cards_6_7": "PASS", "canonical_hashes_required": not allow_noncanonical,
        "executed_supplied_code": False,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path,
                        default=Path(__file__).resolve().with_name("certificate.txt"))
    parser.add_argument("--json", action="store_true", help="emit one JSON result")
    parser.add_argument("--allow-noncanonical", action="store_true",
                        help="skip only raw-certificate and numeric-row expected hashes")
    args = parser.parse_args(argv)
    try:
        result = verify(args.certificate, args.allow_noncanonical)
    except (OSError, InvalidCertificate) as error:
        result = {"status": "FAIL", "checker": "independent_certificate", "error": str(error)}
        print("FAIL: " + str(error), file=sys.stderr)
        if args.json:
            print(json.dumps(result, sort_keys=True))
        return 1
    print(json.dumps(result, sort_keys=True) if args.json else
          "PASS: 2010 rows; 2016 cards; terminal card (P=0, E=389, h=25); all normalization, opening, and continuation checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
