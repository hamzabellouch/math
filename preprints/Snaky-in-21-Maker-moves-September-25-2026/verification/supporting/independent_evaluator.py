#!/usr/bin/env python3
"""Independent strict character parser and explicit-matrix certificate evaluator.
No original verifier code is imported. Integer coordinates and finite sets only.
"""
from dataclasses import dataclass
from pathlib import Path
from collections import Counter
import json
import sys

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
        require(index.isascii() and index.isdigit() and int(index) == self.earlier, 'nonconsecutive card index')
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
        self.cards = [Value(frozenset(p for p in SNAKE if p != omitted), frozenset(SNAKE), 1) for omitted in SNAKE]
        self.expressions = [None] * 6
        self.postorder = []
        self.reference_count = 0
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
    expected = [(648, (4,5), 87,4,35),(708,(8,8),225,4,31),(712,(5,5),96,8,21),
                (713,(5,5),98,4,12),(725,(7,7),167,8,4),(726,(7,7),169,4,0)]
    last = cert.expressions[-1]
    require(last.pivot == (8,8), 'wrong final pivot')
    position = 0
    intersection = None
    rows = []
    for index, sole, size, count, remaining in expected:
        card = cert.cards[index]
        require(card.required == frozenset([sole]) and len(card.support) == size, 'wrong final-group child statistics')
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

def main():
    source = Path(sys.argv[1] if len(sys.argv)>1 else 'certificate.txt')
    out = Path(sys.argv[2] if len(sys.argv)>2 else '.')
    cert = Certificate(source.read_text(encoding='ascii'))
    require(len(cert.cards) == 728, 'wrong card count')
    require(cert.cards[-1].required == frozenset(), 'nonempty final requirement')
    require(len(cert.cards[-1].support) == 251, 'wrong final support cardinality')
    require(cert.cards[-1].height == 21, 'wrong final height')
    for name, values in [('INDEPENDENT-CARDS.json',cert.cards), ('INDEPENDENT-POSTORDER.json',cert.postorder)]:
        (out/name).write_text(json.dumps([encode(v) for v in values],separators=(',',':'))+'\n')
    result={'status':'PASS','cards':len(cert.cards),'listed_combinations':len(cert.cards)-6,
            'all_combinations_including_nested':len(cert.postorder),'nested_combinations':len(cert.postorder)-(len(cert.cards)-6),
            'references':cert.reference_count,'symmetry_counts':dict(cert.symmetry_counts),
            'final':encode(cert.cards[-1]),'final_groups':final_groups(cert),'matrix_checks':matrix_checks(),
            'card_height_histogram':dict(Counter(v.height for v in cert.cards))}
    (out/'INDEPENDENT-RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('final','final_groups')},indent=2))

if __name__ == '__main__':
    main()
