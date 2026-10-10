#!/usr/bin/env python3
"""Exact route-21 reconstruction by recursive token evaluation.

Adapted from the accepted short verifier; all tests use explicit exceptions.
Coordinates in nested combinations remain in the enclosing line's frame.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

DATA_SHA256 = '3fa12d36a6d4dbb185e3f2808c8dfde13d85ee309afbca030d6ad17ae9fe3d04'
SYMBOLS = '0123456789ABCDEFG'
SNAKE = ((0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1))

def require(condition, message):
    if not condition:
        raise ValueError(message)

def check_finite_board(envelope):
    require(all(0 <= x <= 16 and 0 <= y <= 16 for x, y in envelope),
            'final envelope is outside the 17-by-17 board')

def point(word):
    require(len(word) == 2 and all(c in SYMBOLS for c in word), 'invalid point: ' + word)
    return tuple(SYMBOLS.index(c) for c in word)

def put(points, s, dx, dy):
    result = set()
    for x, y in points:
        if s & 2:
            x = -x
        if s & 4:
            y = -y
        if s & 1:
            x, y = y, x
        result.add((x + dx, y + dy))
    require(len(result) == len(points), 'noninjective placement')
    return result

def encode(value):
    a, t, h = value
    return {'A': sorted(a), 'T': sorted(t), 'height': h}

def verify(raw):
    data = raw.decode('ascii')
    require(data.endswith('\n'), 'missing final newline')
    lines = data.splitlines()
    require(len(lines) == 722, 'expected exactly 722 literal rows')
    cards = [(set(SNAKE) - {p}, set(SNAKE), 1) for p in SNAKE]
    postorder, roots = [], []
    references = replies = 0
    def reference(token):
        nonlocal references
        require(re.fullmatch(r'(0|[1-9][0-9]*)(:[0-7][0-9A-G]{2})?', token), 'invalid reference: ' + token)
        parts = token.split(':')
        j = int(parts[0])
        require(j < len(cards), 'reference is not backward')
        s, dx, dy = (0, 0, 0) if len(parts) == 1 else (int(parts[1][0]), *point(parts[1][1:]))
        a, t, h = cards[j]
        references += 1
        return put(a, s, dx, dy), put(t, s, dx, dy), h
    def expression(tokens, position, nested):
        nonlocal replies
        require(position < len(tokens), 'missing pivot')
        pivot = point(tokens[position])
        position += 1
        children = []
        while position < len(tokens) and tokens[position] != ')':
            if tokens[position] == '(':
                child, position, _ = expression(tokens, position + 1, True)
            else:
                child = reference(tokens[position])
                position += 1
            children.append(child)
        if nested:
            require(position < len(tokens) and tokens[position] == ')', 'unclosed inline expression')
            position += 1
        else:
            require(position == len(tokens), 'unmatched closing parenthesis')
        require(children, 'empty child list')
        aa, tt, hh = zip(*children)
        a = (set.union(*aa) | set.intersection(*tt)) - {pivot}
        t = set.union({pivot}, *tt)
        h = 1 + max(hh)
        require(a <= t, 'requirement outside envelope')
        owned = a | {pivot}
        for child_a, child_t, child_h in children:
            require(child_a <= owned, 'missing child requirement')
            require(child_t <= t and child_h < h, 'invalid child budget/envelope')
        for reply in t - owned:
            require(any(reply not in child_t for child_t in tt), 'uncovered internal reply')
            replies += 1
        # Every exterior reply misses all children because child_t <= t.
        replies += 1
        result = (a, t, h)
        postorder.append(result)
        return result, position, (pivot, children)
    for line in lines:
        tokens = line.replace('(', ' ( ').replace(')', ' ) ').split()
        require(len(tokens) >= 3 and tokens[0] == str(len(cards)), 'invalid row index or missing fields')
        value, used, root = expression(tokens, 1, False)
        require(used == len(tokens), 'unconsumed tokens')
        roots.append(root)
        cards.append(value)
    require(len(cards) == 728 and len(postorder) == 1620, 'wrong cardinalities')
    require(references == 4089 and replies == 37042, 'wrong reference/reply counts')
    require(cards[-1][0] == set() and len(cards[-1][1]) == 251 and cards[-1][2] == 21, 'wrong final card')
    check_finite_board(cards[-1][1])
    require(max(c[2] for c in cards) == 21, 'wrong maximum height')
    require(cards[6] == ({(0,y) for y in range(5)}, {(0,y) for y in range(5)} | {(1,3),(1,4),(1,5)}, 2), 'wrong elementary card 6')
    require(cards[7] == ({(0,y) for y in range(1,5)}, {(0,y) for y in range(1,6)} | {(1,y) for y in (0,1,2,4,5,6)}, 3), 'wrong elementary card 7')
    groups = [(648,(4,5),87,15,4,35),(708,(8,8),225,20,4,31),(712,(5,5),96,15,8,21),
              (713,(5,5),98,15,4,12),(725,(7,7),167,20,8,4),(726,(7,7),169,20,4,0)]
    require(roots[-1][0] == (8,8) and len(roots[-1][1]) == 32, 'wrong final pivot/degree')
    used, common = 0, None
    final_tokens = lines[-1].split()[2:]
    for j, sole, size, height, count, remainder in groups:
        require(cards[j][0] == {sole} and len(cards[j][1]) == size and cards[j][2] == height, 'wrong group card')
        for token, child in zip(final_tokens[used:used+count], roots[-1][1][used:used+count]):
            require(int(token.split(':')[0]) == j and child[0] == {(8,8)}, 'wrong final child')
            common = child[1] if common is None else common & child[1]
        require(len(common - {(8,8)}) == remainder, 'wrong cumulative intersection')
        used += count
    require(used == 32 and common == {(8,8)}, 'wrong final intersection')
    # The two example references must be actual children, with composed frames.
    require('708:100' in final_tokens and '684:011' in lines[708-6].split()[2:], 'missing tactical references')
    a, t, _ = cards[708]
    require(put(a,1,0,0) == {(8,8)} and (7,8) not in put(t,1,0,0), 'first tactical envelope')
    require(put({roots[708-6][0]},1,0,0) == {(8,7)}, 'first tactical pivot')
    a, t, _ = cards[684]
    require(put(put(a,0,1,1),1,0,0) <= {(8,8),(8,7)}, 'second tactical requirement')
    require(not (put(put(t,0,1,1),1,0,0) & {(7,8),(8,6)}), 'second tactical envelope')
    require(put(put({roots[684-6][0]},0,1,1),1,0,0) == {(11,8)}, 'second tactical pivot')
    return {'cards': [encode(c) for c in cards], 'postorder': [encode(c) for c in postorder],
            'counts': {'cards':728, 'numbered_rows':722, 'inline_nodes':898, 'combination_nodes':1620,
                       'references':references, 'reply_classes':replies},
            'endpoint': {'A_size':0, 'T_size':251, 'height':21, 'pivot':[8,8]},
            'top_intersections':[g[-1] for g in groups],
            'tactics': {'708_pivot':[8,7], '684_composed_pivot':[11,8], 'old_and_new_replies_avoided':True}}

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
