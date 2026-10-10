#!/usr/bin/env python3
"""Independent finite path-system deduction engine; Python standard library only.

No imports or calls to the supplied checker. Canonical patterns are built by
integer partitions of component orders. Graph edges are unordered pairs; old
paths and their extensions are explicit vertex lists. Forbidden parameters use
integer flags on unordered pairs. Simple paths use frozenset/endpoint states.
Packing search branches on centers, not on individual graph vertices/options.
Every accepted pattern has a retained JSON proof trace and a final witness.
The mathematical meaning of these deductions is conditional on the lemmas
in the paper's finite-case section and accompanying reproduction instructions.
"""
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path
import argparse
import hashlib
import json
import time


def partitions(total, least=1):
    if total == 0:
        yield ()
    for first in range(least, total + 1):
        for tail in partitions(total - first, first):
            yield (first,) + tail


def compositions(total, length):
    if length == 0:
        if total == 0:
            yield ()
        return
    for first in range(1, total - length + 2):
        for tail in compositions(total - first, length - 1):
            yield (first,) + tail


def patterns(t, budget):
    chain = {}
    for order in range(1, t + 1):
        chain[order] = sorted({min(c, c[::-1]) for amount in range(budget + 1)
                               for c in compositions(amount, order - 1)})
    answer = set()
    for sizes in partitions(t):
        groups = []
        for order, count in Counter(sizes).items():
            groups.append([g for g in combinations_with_replacement(chain[order], count)
                           if sum(map(sum, g)) <= budget])
        for groups_choice in product(*groups):
            p = tuple(sorted(c for group in groups_choice for c in group))
            if sum(map(sum, p)) <= budget:
                answer.add(p)
    return sorted(answer)


def key(x, y):
    assert x != y
    return (min(x, y), max(x, y))


def graph(p):
    """Labels deliberately agree for comparison; structure is explicit lists."""
    clique, paths, offset = [], [], 0
    for chain in p:
        clique.append(offset)
        for amount in chain:
            path = tuple(range(offset, offset + amount + 2))
            paths.append(path)
            offset = path[-1]
            clique.append(offset)
        offset += 1
    required = {key(x, y) for x, y in combinations(clique, 2)}
    for path in paths:
        required.update(key(x, y) for x, y in zip(path, path[1:]))
    return offset, frozenset(clique), tuple(paths), frozenset(required)


def segments(x, clique, paths):
    if x in clique:
        return [(x,)]
    containing = [p for p in paths if x in p[1:-1]]
    assert len(containing) == 1
    p = containing[0]
    index = p.index(x)
    return [p[:index+1][::-1], p[index:]]  # x-to-clique lists


def linear_forest(paths):
    """Check max degree 2 and acyclicity by undirected union/find."""
    parent, degree = {}, Counter()
    def root(x):
        while parent[x] != x:
            x = parent[x]
        return x
    for path in paths:
        x, y = path[0], path[-1]
        if x == y:
            return False
        parent.setdefault(x, x)
        parent.setdefault(y, y)
        degree[x] += 1
        degree[y] += 1
        if degree[x] > 2 or degree[y] > 2 or root(x) == root(y):
            return False
        parent[root(x)] = root(y)
    return True


def initial_constraints(k, t, n, clique, paths):
    """Construct actual splices, then test optimality/forbidden interval."""
    restrictions = {}
    amount = n - t
    h = k + 1 - t
    for x, y in combinations(range(n), 2):
        flags = 0
        eligible = [p for p in paths if x not in p[1:-1] and y not in p[1:-1]]
        for sx, sy in product(segments(x, clique, paths), segments(y, clique, paths)):
            # A valid new path uses disjoint extensions and distinct endpoints.
            if set(sx) & set(sy) or sx[-1] >= sy[-1]:
                continue
            for number in range(len(eligible) + 1):
                for selected in combinations(eligible, number):
                    # Placeholder -1 stands for the hypothesized outside path.
                    new_path = tuple(reversed(sx)) + (-1,) + sy
                    candidate = selected + (new_path,)
                    if not linear_forest(candidate):
                        continue
                    incident = {v for path in candidate for v in (path[0], path[-1])}
                    fixed = sum(len(p)-2 for p in selected) + len(sx)+len(sy)-2
                    for d in range(1, k + 1):
                        q = fixed + d
                        improves = q < h and (q > amount or
                                               (q == amount and len(candidate) < len(paths)))
                        closes_cycle = h <= q <= k+1-len(incident)
                        if improves or closes_cycle:
                            flags |= 1 << d
        if flags:
            restrictions[x, y] = flags
    return restrictions


def adjacency(n, required):
    neighbors = [set() for _ in range(n)]
    for x, y in required:
        neighbors[x].add(y)
        neighbors[y].add(x)
    return neighbors


def path_constraints(k, n, required, old):
    """Enumerate simple paths with ordinary vertex sets, not integer masks."""
    constraints = dict(old)
    neighbors = adjacency(n, required)
    for start in range(n):
        states = {(frozenset({start}), start)}
        for length in range(1, k + 1):
            following = set()
            for visited, end in states:
                for nxt in neighbors[end] - visited:
                    following.add((visited | {nxt}, nxt))
                    pair = key(start, nxt)
                    constraints[pair] = constraints.get(pair, 0) | (1 << (k-length))
            states = following
            if not states:
                break
    return constraints


def range_flags(last):
    return (1 << (last+1)) - 2


def ball_options(k, t, n, restrictions):
    groups = []
    for center in range(n):
        row = [restrictions.get(key(center, j), 0) for j in range(n) if j != center]
        options = [(center, -1, 1)]
        size = k + 1 - n + sum(bool(flags & 1) for flags in row)
        if size > 0:
            weight = 2 if size >= t else 1
            options.append((center, 0, weight))
            for radius in (1, 2):
                prefix = range_flags(radius)
                misses = sum((flags & prefix) == prefix for flags in row)
                next_size = max(size, k*weight + 1 - n + misses)
                next_weight = max(weight, 1 + (next_size > t) +
                                  (next_size > max(k, 2*t)))
                if (next_weight == 1 and size == next_size == t and
                        k + 1 - n + misses >= t):
                    next_weight = 2
                # Keep ALL radii. The search therefore does not rely on pruning
                # equal-weight, larger-radius options as the source does.
                options.append((center, radius, next_weight))
                size, weight = next_size, next_weight
        groups.append(tuple(options))
    return tuple(groups)


def packing(k, t, n, restrictions):
    """Branch per center: choose a permissible radius or omit the center."""
    groups = ball_options(k, t, n, restrictions)
    def compatible(a, b):
        length = a[1] + b[1] + 2
        need = 1 if length == 0 else range_flags(length)
        return (restrictions.get(key(a[0], b[0]), 0) & need) == need
    @lru_cache(None)
    def search(available, deficit):
        if deficit < 0:
            return ()
        if sum(max(o[2] for o in group) for group in available) <= deficit:
            return None
        # Every branch chooses a center, with at most four radius options.
        head = min(available, key=lambda group: (-max(o[2] for o in group), len(group)))
        tail = tuple(group for group in available if group is not head)
        # Tuples are immutable, but identity removal remains valid here because
        # distinct groups have different first coordinates and cannot alias.
        for option in sorted(head, key=lambda o: (-o[2], o[1])):
            filtered = tuple(tuple(p for p in group if compatible(option, p)) for group in tail)
            filtered = tuple(group for group in filtered if group)
            result = search(filtered, deficit-option[2])
            if result is not None:
                return (option,) + result
        return search(tail, deficit)
    witness = search(groups, k)
    if witness is not None:
        assert sum(o[2] for o in witness) > k
        assert len({o[0] for o in witness}) == len(witness)
        assert all(compatible(a, b) for a, b in combinations(witness, 2))
    return witness


def contradiction(k, t, n, required, restrictions):
    for edge in sorted(required):
        if restrictions.get(edge, 0) & 1:
            return {'kind': 'required_forbidden_edge', 'edge': edge}
    witness = packing(k, t, n, restrictions)
    if witness is not None:
        return {'kind': 'packing', 'options': witness, 'weight': sum(o[2] for o in witness)}
    return None


def serialized(restrictions):
    return [[x, y, flags] for (x, y), flags in sorted(restrictions.items())]


def check_pattern(k, t, p):
    n, clique, paths, required = graph(p)
    constraints = initial_constraints(k, t, n, clique, paths)
    trace = {'k': k, 't': t, 'pattern': p, 'initial': serialized(constraints), 'rounds': []}
    witness = packing(k, t, n, constraints)
    if witness is not None:
        trace.update(classification=1, final={'kind': 'packing', 'options': witness,
                                            'weight': sum(o[2] for o in witness)})
        return trace
    constraints = path_constraints(k, n, required, constraints)
    while True:
        final = contradiction(k, t, n, required, constraints)
        if final is not None:
            trace.update(classification=2, final=final)
            return trace
        new = []
        for x, y in combinations(range(n), 2):
            for d in (0, 1):
                if constraints.get((x, y), 0) & (1 << d) or (d == 0 and (x, y) in required):
                    continue
                extension = {(x, y)} if d == 0 else {key(x, n), key(y, n)}
                hyp_required = required | extension
                hyp_constraints = path_constraints(k, n+d, hyp_required, constraints)
                reason = contradiction(k, t, n+d, hyp_required, hyp_constraints)
                if reason is not None:
                    new.append({'pair': (x, y), 'd': d, 'witness': reason})
        if not new:
            trace.update(classification=0, final=None, residual=serialized(constraints))
            return trace
        trace['rounds'].append(new)
        for addition in new:
            pair = tuple(addition['pair'])
            constraints[pair] = constraints.get(pair, 0) | (1 << addition['d'])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--min-k', type=int, default=5)
    parser.add_argument('--max-k', type=int, default=17)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    begin = time.perf_counter()
    counts, coverage = {}, []
    with (args.output/'certificates.jsonl').open('w') as out:
        for k in range(args.min_k, args.max_k + 1):
            counts[k] = [0, 0, 0]
            for t in range(max(3, k//2), min(k, 8)+1):
                all_patterns = patterns(t, k-t)
                coverage.append({'k': k, 't': t, 'patterns': len(all_patterns),
                                 'by_amount': dict(sorted(Counter(sum(map(sum, p)) for p in all_patterns).items()))})
                for p in all_patterns:
                    record = check_pattern(k, t, p)
                    counts[k][record['classification']] += 1
                    out.write(json.dumps(record, separators=(',', ':'))+'\n')
            out.flush()
            print(k, *counts[k], flush=True)
    summary = {'counts': counts, 'coverage': coverage, 'total_patterns': sum(map(sum, counts.values())),
               'unresolved': sum(c[0] for c in counts.values()),
               'runtime_seconds': time.perf_counter()-begin,
               'implementation_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'certificates_sha256': hashlib.sha256((args.output/'certificates.jsonl').read_bytes()).hexdigest()}
    (args.output/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    assert summary['unresolved'] == 0, summary


if __name__ == '__main__':
    main()
