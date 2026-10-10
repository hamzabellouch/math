"""Independent structural and finite checks for the submitted capacity code."""
import ast
import inspect
import time

import capacity_checks as submitted


def partitions(n, cap=None):
    if not n:
        yield ()
        return
    cap = n if cap is None else min(cap, n)
    for first in range(cap, 0, -1):
        for rest in partitions(n-first, first):
            yield (first,) + rest


def conjugate(a):
    return tuple(sum(x >= i for x in a) for i in range(1, a[0]+1)) if a else ()


def hook_enumeration(n):
    output = []

    def gen(left, a, b):
        k = len(a)
        if not left:
            u = a + tuple(sum(z >= i for z in b) for i in range(k+1, b[0]+1))
            v = b + tuple(sum(z >= i for z in a) for i in range(k+1, a[0]+1))
            assert sum(u) == n and conjugate(u) == v
            output.append(u)
            return
        for x in range(1, 1+min(left, a[-1]-k if a else n)):
            for y in range((left+x-1)//x,
                           1+min(left+1-x, b[-1]-k if b else x)):
                gen(left+1-x-y, a+(x+k,), b+(y+k,))

    gen(n, (), ())
    return output


def setup(m, r):
    # Return the submitted run's exact local functions before enumeration.
    tree = ast.parse(inspect.getsource(submitted.run))
    tree.body[0].body[-1] = ast.parse('return locals()').body[0]
    ast.fix_missing_locations(tree)
    namespace = vars(submitted).copy()
    exec(compile(tree, '<submitted setup>', 'exec'), namespace)
    return namespace['run'](m, r)


def horizontal_strip(a, b):
    if any(x > y for x, y in zip(b, a+(0,)*len(b))):
        return False
    ac = conjugate(a)
    bc = conjugate(b)
    return all(x-(bc[i] if i < len(bc) else 0) in (0, 1)
               for i, x in enumerate(ac))


def prefix_support(A, h):
    return all(sum(h[:i]) <= sum(min(i, a) for a in A)
               for i in range(1, max(max(A), len(h))+1))


def main():
    started = time.monotonic()
    total = 0
    for n in range(1, 41):
        actual = hook_enumeration(n)
        expected = {p for p in partitions(n) if p[0] >= len(p)}
        assert len(actual) == len(set(actual))
        assert set(actual) == expected
        total += len(actual)
    print('PASS diagonal-hook coverage n=1..40 representatives=%d' % total, flush=True)

    mask_cases = 0
    for m in (10, 12, 14):
        for r in range({10:8, 12:14, 14:22}[m], 3*m//2+3):
            d = setup(m, r)
            n, c, s = d['n'], d['c'], d['s']
            assert all(sum(a) == n for a in d['B'])
            assert all(sum(a) == n-(d['K']+r) for a in d['C'])
            ev = {p for p in partitions(c) if len(p) <= 3 and all(x%2 == 0 for x in p)}
            step = {p for p in partitions(c+3) if len(p) <= 3
                    and any(horizontal_strip(p, b) for b in ev)}
            good = {p for p in partitions(c+3+s) if len(p) <= 3
                    and any(horizontal_strip(p, b) for b in step)}
            assert ev == set(d['ev'])
            assert step == set(d['step'])
            assert good == set(d['tot'])-set(d['bad'])
            mask_cases += 1
    print('PASS exceptional B/C total sizes and independent Pieri masks cases=%d' % mask_cases,
          flush=True)

    bound = setup(10, 8)['bound']
    checked = 0
    for n in range(1, 17):
        ps = list(partitions(n))
        for A in ps:
            for h in ps:
                actual = prefix_support(A, h)
                for size in range(1, len(h)+1):
                    assert not bound(A, h[:size]) or actual
                    checked += 1
                assert bound(A, h+(0,)) == actual
    print('PASS conservative bound n=1..16 prefix_checks=%d' % checked, flush=True)
    print('PASS all independent checks elapsed_seconds=%.6f' % (time.monotonic()-started),
          flush=True)


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Capacity verification requires assertions; run Python without -O.')
    main()
