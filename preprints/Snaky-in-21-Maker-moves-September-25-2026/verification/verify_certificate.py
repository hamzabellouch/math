def verify(data):
    symbols = '0123456789ABCDEFG'
    snake = [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)]
    TT = [set(snake) for _ in snake]
    AA = [t - {p} for t, p in zip(TT, snake)]
    HH = [1 for _ in snake]
    def point(x):
        assert len(x) == 2
        return tuple(symbols.index(c) for c in x)
    def reference(token):
        parts = token.split(':')
        j = int(parts[0])
        assert 0 <= j < len(AA)
        if len(parts) == 1:
            s = dx = dy = 0
        else:
            assert len(parts) == 2 and len(parts[1]) == 3
            s = int(parts[1][0])
            assert 0 <= s < 8
            dx, dy = point(parts[1][1:])
        def put(P):
            Q = set()
            for x, y in P:
                if s & 2:
                    x = -x
                if s & 4:
                    y = -y
                if s & 1:
                    x, y = y, x
                Q.add((x + dx, y + dy))
            return Q
        return put(AA[j]), put(TT[j]), HH[j]
    def expr(it):
        p = point(next(it))
        aa, tt, hh = [], [], []
        while True:
            word = next(it)
            if word == ')':
                break
            a, t, h = expr(it) if word == '(' else reference(word)
            aa.append(a)
            tt.append(t)
            hh.append(h)
        assert aa
        return ((set.union(*aa) | set.intersection(*tt)) - {p},
                set.union({p}, *tt), 1 + max(hh))
    for line in data.strip().splitlines():
        words = line.replace('(', ' ( ').replace(')', ' ) ').split()
        it = iter(words + [')'])
        assert int(next(it)) == len(AA)
        a, t, h = expr(it)
        assert a <= t
        assert next(it, None) is None
        AA.append(a)
        TT.append(t)
        HH.append(h)
    assert len(AA) == 728 and len(TT[-1]) == 251
    assert all(0 <= x <= 16 and 0 <= y <= 16 for x, y in TT[-1])
    assert AA[-1] == set()
    assert HH[-1] == 21
    # Additional checks for the stated intermediate table and examples.
    assert max(HH) == 21
    assert AA[6] == {(0, y) for y in range(5)}
    assert TT[6] == AA[6] | {(1, 3), (1, 4), (1, 5)}
    assert AA[7] == {(0, y) for y in range(1, 5)}
    assert words[:2] == ['727', '88']
    final_children = words[2:]
    assert len(final_children) == 32
    groups = [
        (648, (4, 5), 87, 15, 4, 35),
        (708, (8, 8), 225, 20, 4, 31),
        (712, (5, 5), 96, 15, 8, 21),
        (713, (5, 5), 98, 15, 4, 12),
        (725, (7, 7), 167, 20, 8, 4),
        (726, (7, 7), 169, 20, 4, 0),
    ]
    used, common = 0, None
    for j, required_cell, size, height, count, remainder in groups:
        assert AA[j] == {required_cell}
        assert len(TT[j]) == size and HH[j] == height
        for token in final_children[used:used + count]:
            assert int(token.split(':')[0]) == j
            a, t, h = reference(token)
            assert a == {(8, 8)}
            common = t if common is None else common & t
        assert len(common - {(8, 8)}) == remainder
        used += count
    assert used == len(final_children)
    assert common == {(8, 8)}


def main():
    import argparse
    import hashlib
    import json
    from pathlib import Path
    import sys

    if not __debug__:
        raise SystemExit("Verification requires assertions; do not use python -O.")
    parser = argparse.ArgumentParser(description="Check the exact 21-turn Snaky certificate.")
    parser.add_argument("--table", type=Path,
                        default=Path(__file__).with_name("certificate.txt"))
    args = parser.parse_args()
    payload = args.table.read_bytes()
    digest = hashlib.sha256(payload).hexdigest()
    expected = "3fa12d36a6d4dbb185e3f2808c8dfde13d85ee309afbca030d6ad17ae9fe3d04"
    if digest != expected:
        raise SystemExit("Certificate SHA256 mismatch: " + digest)
    data = payload.decode("ascii")
    verify(data)
    print(json.dumps({"status": "PASS", "certificate_sha256": digest,
                      "numbered_cards": 728, "final_index": 727,
                      "final_required_cells": 0, "final_support_cells": 251,
                      "final_height": 21}, sort_keys=True))


if __name__ == "__main__":
    main()
