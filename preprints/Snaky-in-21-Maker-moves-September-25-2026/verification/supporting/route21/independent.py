#!/usr/bin/env python3
"""Independent strict character parser and explicit-matrix certificate evaluator.
No original verifier code is imported. Integer coordinates and finite sets only.
"""
from dataclasses import dataclass
from pathlib import Path
from collections import Counter
import json
import sys
import argparse
import hashlib

DATA_SHA256 = '3fa12d36a6d4dbb185e3f2808c8dfde13d85ee309afbca030d6ad17ae9fe3d04'

DIGITS = '0123456789ABCDEFG'
MATRICES = (
    ((1, 0), (0, 1)), ((0, 1), (1, 0)),
    ((-1, 0), (0, 1)), ((0, 1), (-1, 0)),
    ((1, 0), (0, -1)), ((0, -1), (1, 0)),
    ((-1, 0), (0, -1)), ((0, -1), (-1, 0)),
)
SNAKE = ((0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1))

def require(condition, message):
    if not condition:
        raise ValueError(message)

def check_finite_board(envelope):
    square = frozenset((x, y) for x in range(17) for y in range(17))
    require(frozenset(envelope) <= square,
            'final envelope is outside the 17-by-17 board')

def point(word):
    require(len(word) == 2 and all(c in DIGITS for c in word), 'bad coordinate ' + word)
    return (DIGITS.index(word[0]), DIGITS.index(word[1]))

@dataclass(frozen=True)
class Reference:
    card: int
    symmetry: int = 0
    shift: tuple = (0, 0)

@dataclass(frozen=True)
class Combination:
    pivot: tuple
    children: tuple

@dataclass(frozen=True)
class Value:
    required: frozenset
    support: frozenset
    height: int

class Parser:
    def __init__(self, line, earlier):
        self.line, self.pos, self.earlier = line, 0, earlier

    def space(self):
        while self.pos < len(self.line) and self.line[self.pos].isspace():
            self.pos += 1

    def word(self):
        self.space()
        start = self.pos
        while self.pos < len(self.line) and not self.line[self.pos].isspace() and self.line[self.pos] not in '()':
            self.pos += 1
        require(self.pos > start, 'expected word at ' + str(start))
        return self.line[start:self.pos]

    def reference(self):
        token = self.word()
        parts = token.split(':')
        require(len(parts) in (1, 2), 'too many colons')
        require(parts[0] and all('0' <= c <= '9' for c in parts[0]), 'invalid decimal reference')
        index = int(parts[0])
        require(str(index) == parts[0], 'noncanonical decimal reference')
        require(index < self.earlier, 'reference is not an earlier card')
        if len(parts) == 1:
            return Reference(index)
        code = parts[1]
        require(len(code) == 3 and code[0] in '01234567', 'invalid placement')
        return Reference(index, int(code[0]), point(code[1:]))

    def combination(self, nested):
        pivot = point(self.word())
        children = []
        while True:
            self.space()
            if self.pos == len(self.line):
                require(not nested, 'missing closing parenthesis')
                break
            ch = self.line[self.pos]
            if ch == ')':
                require(nested, 'unexpected closing parenthesis')
                self.pos += 1
                break
            if ch == '(':
                self.pos += 1
                children.append(self.combination(True))
            else:
                children.append(self.reference())
        require(children, 'empty child list')
        return Combination(pivot, tuple(children))

    def card(self):
        index = self.word()
        require(index == str(self.earlier), 'nonconsecutive or noncanonical card index')
        expression = self.combination(False)
        self.space()
        require(self.pos == len(self.line), 'trailing content')
        return expression

def transform_point(p, symmetry, shift):
    m = MATRICES[symmetry]
    return (m[0][0]*p[0]+m[0][1]*p[1]+shift[0],
            m[1][0]*p[0]+m[1][1]*p[1]+shift[1])

def transform(value, symmetry, shift):
    a = frozenset(transform_point(p, symmetry, shift) for p in value.required)
    t = frozenset(transform_point(p, symmetry, shift) for p in value.support)
    require(len(a) == len(value.required) and len(t) == len(value.support), 'placement lost cells')
    return Value(a, t, value.height)

class Certificate:
    def __init__(self, data):
        require(data.endswith('\n'), 'missing final newline')
        require(len(data.splitlines()) == 722, 'wrong literal row count')
        self.cards = [Value(frozenset(p for p in SNAKE if p != omitted), frozenset(SNAKE), 1) for omitted in SNAKE]
        self.expressions = [None] * 6
        self.postorder = []
        self.reference_count = 0
        self.reply_classes = 0
        self.symmetry_counts = Counter()
        for line in data.splitlines():
            require(bool(line.strip()), 'blank certificate line')
            tree = Parser(line, len(self.cards)).card()
            result = self.evaluate(tree)
            self.expressions.append(tree)
            self.cards.append(result)

    def evaluate(self, tree):
        if isinstance(tree, Reference):
            self.reference_count += 1
            self.symmetry_counts[tree.symmetry] += 1
            return transform(self.cards[tree.card], tree.symmetry, tree.shift)
        children = tuple(self.evaluate(child) for child in tree.children)
        support = frozenset([tree.pivot] + [p for child in children for p in child.support])
        required = frozenset(p for p in support if p != tree.pivot and (
            any(p in child.required for child in children) or all(p in child.support for child in children)))
        result = Value(required, support, 1 + max(child.height for child in children))
        require(result.required <= result.support, 'required set escapes support')
        owned = result.required | {tree.pivot}
        require(all(child.required <= owned and child.support <= result.support and child.height < result.height for child in children), 'child invariant failure')
        for reply in result.support - owned:
            require(any(reply not in child.support for child in children), 'uncovered internal reply')
            self.reply_classes += 1
        # One exact exterior equivalence class: every child envelope is contained.
        self.reply_classes += 1
        self.postorder.append(result)
        return result

def encode(v):
    return {'A': sorted(v.required), 'T': sorted(v.support), 'height': v.height}

def matrix_checks():
    import itertools
    brute = set()
    for permutation in ((0,1), (1,0)):
        for signs in itertools.product((-1,1), repeat=2):
            rows = []
            for i in range(2):
                rows.append(tuple(signs[i] if j == permutation[i] else 0 for j in range(2)))
            brute.add(tuple(rows))
    require(set(MATRICES) == brute, 'matrix table not exactly signed coordinate permutations')
    for a in MATRICES:
        for b in MATRICES:
            product = tuple(tuple(sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)) for i in range(2))
            require(product in brute, 'symmetries not closed')
    return {'distinct_signed_permutation_matrices': len(brute), 'composition_pairs_checked':64}

def final_groups(cert):
    expected = [(648, (4,5), 87,15,4,35),(708,(8,8),225,20,4,31),(712,(5,5),96,15,8,21),
                (713,(5,5),98,15,4,12),(725,(7,7),167,20,8,4),(726,(7,7),169,20,4,0)]
    last = cert.expressions[-1]
    require(last.pivot == (8,8), 'wrong final pivot')
    position = 0
    intersection = None
    rows = []
    for index, sole, size, height, count, remaining in expected:
        card = cert.cards[index]
        require(card.required == frozenset([sole]) and len(card.support) == size and card.height == height, 'wrong final-group child statistics')
        group = last.children[position:position+count]
        for ref in group:
            require(isinstance(ref,Reference) and ref.card == index, 'unexpected final child order')
            child = transform(card, ref.symmetry, ref.shift)
            require(child.required == frozenset([last.pivot]), 'placed requirement is not final pivot')
            intersection = child.support if intersection is None else intersection & child.support
        require(len(intersection - {last.pivot}) == remaining, 'incorrect cumulative intersection size')
        rows.append({'index':index,'A':sorted(card.required),'T_size':size,'placements':count,
                     'remaining':remaining,'height':card.height,'intersection':sorted(intersection)})
        position += count
    require(position == len(last.children), 'extra final children')
    return rows

def verify(raw):
    cert = Certificate(raw.decode('ascii'))
    require(len(cert.cards) == 728, 'wrong card count')
    require(cert.cards[-1].required == frozenset(), 'nonempty final requirement')
    require(len(cert.cards[-1].support) == 251, 'wrong final support cardinality')
    check_finite_board(cert.cards[-1].support)
    require(cert.cards[-1].height == 21, 'wrong final height')
    require(max(c.height for c in cert.cards) == 21, 'wrong maximum height')
    require(len(cert.postorder) == 1620 and cert.reference_count == 4089 and cert.reply_classes == 37042, 'wrong reconstruction counts')
    require(cert.cards[6] == Value(frozenset((0,y) for y in range(5)),frozenset((0,y) for y in range(5))|{(1,3),(1,4),(1,5)},2), 'wrong elementary card 6')
    require(cert.cards[7] == Value(frozenset((0,y) for y in range(1,5)),frozenset((0,y) for y in range(1,6))|{(1,y) for y in (0,1,2,4,5,6)},3), 'wrong elementary card 7')
    first = Reference(708,1,(0,0))
    second = Reference(684,0,(1,1))
    require(first in cert.expressions[727].children and second in cert.expressions[708].children, 'missing tactical child references')
    a = transform(cert.cards[708],1,(0,0))
    require(a.required == {(8,8)} and (7,8) not in a.support, 'first tactical envelope')
    require(transform_point(cert.expressions[708].pivot,1,(0,0)) == (8,7), 'first tactical pivot')
    b = transform(transform(cert.cards[684],0,(1,1)),1,(0,0))
    require(b.required <= {(8,8),(8,7)} and not (b.support & {(7,8),(8,6)}), 'second tactical envelope')
    require(transform_point(transform_point(cert.expressions[684].pivot,0,(1,1)),1,(0,0)) == (11,8), 'second tactical pivot')
    return {'cards':[encode(v) for v in cert.cards], 'postorder':[encode(v) for v in cert.postorder],
            'counts': {'cards':728, 'numbered_rows':722, 'inline_nodes':898, 'combination_nodes':1620,
                       'references':cert.reference_count, 'reply_classes':cert.reply_classes},
            'endpoint': {'A_size':0, 'T_size':251, 'height':21, 'pivot':[8,8]},
            'top_intersections':[g['remaining'] for g in final_groups(cert)],
            'tactics': {'708_pivot':[8,7], '684_composed_pivot':[11,8], 'old_and_new_replies_avoided':True},
            'matrix_checks':matrix_checks(),
            'card_height_histogram':dict(Counter(v.height for v in cert.cards))}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--table', type=Path, default=Path(__file__).with_name('certificate.txt'))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    raw = args.table.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == DATA_SHA256, 'literal SHA256 mismatch')
    result = verify(raw)
    if args.output:
        args.output.write_text(json.dumps(result, separators=(',',':'), sort_keys=True) + '\n')
    print(json.dumps({'status':'PASS', 'certificate_sha256':DATA_SHA256, **{k:v for k,v in result.items() if k not in ('cards','postorder')}}, sort_keys=True))

if __name__ == '__main__':
    main()
