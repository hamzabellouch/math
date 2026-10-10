#!/usr/bin/env python3
"""Independent exact expansion of the bernoulli-critical-dimension interior certificate.

Origin: written from input.md's mathematical definitions and literal tables,
with no consultation of the optional submitted Python or any older verifier.
Only the Python standard library and separately authored bounds.py are used.

An edge joins matrix-power paths. Vertices 0..4 are free indices, 5 and 6
are occurrences of p and ell, and 7/8 are symmetric third-order tensors X.
Vertices >=100 are dummy indices and must have valency two; eliminating them
concatenates paths. This implements contractions before coefficient collection.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
import hashlib
from itertools import islice, permutations
import json
from pathlib import Path
import time

Q = 250000
AEXP = Fraction(29, 50)
ZERO = (0, 0, 0, (), ())
RANKS = {'f': 0, 'U': 2, 'K': 4, 'M': 1, 'P': 1}


@lru_cache(maxsize=100000)
def canonical(raw):
    """Eliminate valency-two dummy vertices and use precisely stated relations."""
    h, w, z, old_traces, old_edges = raw
    traces, edges = list(old_traces), list(old_edges)
    while True:
        internal = next((v for e in edges for v in e[:2] if v >= 100), None)
        if internal is None:
            break
        hits = [i for i, e in enumerate(edges) if internal in e[:2]]
        if len(hits) == 1:
            u, v, k = edges.pop(hits[0])
            assert u == v == internal, ('dangling index', raw, internal)
            traces.append(k)
        else:
            assert len(hits) == 2, ('invalid valency', raw, internal)
            j, i = sorted(hits, reverse=True)
            e2, e1 = edges.pop(j), edges.pop(i)
            u = e1[1] if e1[0] == internal else e1[0]
            v = e2[1] if e2[0] == internal else e2[0]
            edges.append((u, v, e1[2] + e2[2]))
    factor = 1
    kept = []
    for k in traces:
        if k == 0:
            factor *= 5
        elif k == 1:
            return 0, ZERO
        elif k != 2:
            kept.append(k)
    if any(u == v and u in (7, 8) and k == 0 for u, v, k in edges):
        return 0, ZERO
    def edge_form(mapping):
        return tuple(sorted((min(mapping.get(u,u),mapping.get(v,v)),
                             max(mapping.get(u,u),mapping.get(v,v)),k)
                            for u,v,k in edges))
    original = edge_form({})
    exchanged = edge_form({7:8,8:7})
    return factor, (h,w,z,tuple(sorted(kept)),min(original,exchanged))


def build(h=0,w=0,z=0,traces=(),edges=()):
    return canonical((h,w,z,tuple(traces),tuple(edges)))


def parse_monomial(code, rank):
    assert len(code) % 3 == 0
    h,b,j = map(int,code[:3])
    assert j in (0,1,2)
    triples = [tuple(map(int,code[i:i+3])) for i in range(3,len(code),3)]
    counts = Counter(x for e in triples for x in e[:2])
    assert all(counts[i] == 1 for i in range(rank)), (code,rank,counts)
    assert not any(i in counts for i in range(rank,5)), (code,rank)
    factor,key = build(h,j==1,j==2,(3,)*b,triples)
    assert factor == 1, (code,factor)
    return key


def remap(key, mapping, *, dh=0,dw=0,dz=0,extra_edges=(),extra_traces=()):
    h,w,z,t,e = key
    edges = [(mapping.get(u,u),mapping.get(v,v),k) for u,v,k in e]
    edges += list(extra_edges)
    return build(h+dh,w+dw,z+dz,t+tuple(extra_traces),edges)


def accum(out, coefficient, result):
    factor,key = result
    if factor and coefficient:
        out[key] += coefficient*factor


def clean(poly):
    return {k:v for k,v in poly.items() if v}


def gradient(key, rank):
    """Product rule; the derivative index is appended as free slot rank."""
    h,w,z,t,edges = key
    assert not any(v in (7,8) for e in edges for v in e[:2])
    assert w == z == 0  # Table-I tensors contain A,p,g only.
    out = defaultdict(Fraction)
    if h:
        accum(out,h,remap(key,{},dh=-1,dz=1,extra_edges=((5,rank,0),)))
    # Each p endpoint is differentiated separately, even on a p--p edge.
    for ei,(u,v,k) in enumerate(edges):
        for side,endpoint in enumerate((u,v)):
            if endpoint != 5:
                continue
            other = v if side == 0 else u
            rest = edges[:ei]+edges[ei+1:]
            accum(out,1,build(h,1,0,t,rest+((rank,other,k+1),)))
            accum(out,-1,build(h+1,0,1,t,rest+((rank,other,k),)))
        for split in range(k):
            rest = edges[:ei]+edges[ei+1:]
            new = ((u,7,split),(7,v,k-1-split),(7,rank,0))
            accum(out,1,build(h,0,0,t,rest+new))
    for ti,k in enumerate(t):
        rest = t[:ti]+t[ti+1:]
        accum(out,k,build(h,0,0,rest,edges+((7,7,k-1),(7,rank,0))))
    degree = sum(t)+sum(e[2] for e in edges)
    if degree:
        accum(out,-degree,remap(key,{},extra_edges=((7,7,1),(7,rank,0))))
    return clean(out)


def scalar_close(key, closing_edges=(), mapping=None, *, dh=0,dw=0,dz=0):
    """Close all indicated free-index paths by adding a matching of edges."""
    if mapping is None:
        mapping = {i:100+i for i in range(5)}
        closing_edges = tuple((100+u,100+v,k) for u,v,k in closing_edges)
    result = remap(key,mapping,dh=dh,dw=dw,dz=dz,extra_edges=closing_edges)
    if result[0]:
        assert all(v>=5 for e in result[1][4] for v in e[:2]), result
    return result


def contract_G_with_X(key):
    # l and derivative l close; i,j,k become the three slots of a new X.
    labels = {v for e in key[4] for v in e[:2]}
    new_x = 8 if 7 in labels or 8 in labels else 7
    return scalar_close(key,mapping={0:100,4:100,1:new_x,2:new_x,3:new_x})


def q_times(key, free):
    assert not any(v in (7,8) for e in key[4] for v in e[:2])
    return remap(key,{},extra_edges=((7,7,1),(7,free,0)))


def row_interior(name, key):
    """Contribution of one Table-I monomial to the displayed I polynomial."""
    out = defaultdict(Fraction)
    if name == 'f':
        accum(out,-4,remap(key,{},dz=2))
        accum(out,1,remap(key,{},extra_edges=((6,6,0),)))
        for grad,c in gradient(key,0).items():
            accum(out,-c,scalar_close(grad,mapping={0:6}))
        fact,qf = q_times(key,0)
        accum(out,-2*AEXP*fact,scalar_close(qf,mapping={0:6}))
    elif name in ('M','P'):
        # w div M +(2a+1)w q.M; z div P+2a z q.P.
        shift = {'dw':1} if name=='M' else {'dz':1}
        for grad,c in gradient(key,1).items():
            accum(out,c,scalar_close(grad,mapping={0:100,1:100},**shift))
        fact,qv = q_times(key,1)
        rate = 2*AEXP+(name=='M')
        accum(out,rate*fact,scalar_close(qv,mapping={0:100,1:100},**shift))
    else:
        # Build the relevant G. U is inserted as delta_li U_jk.
        if name == 'U':
            accum(out,5,scalar_close(key,((0,1,1),),dz=2))
            fact,gkey = remap(key,{0:2,1:3},extra_edges=((0,1,0),))
            gp = {gkey:fact}
        else:
            assert name == 'K'
            gp0 = defaultdict(Fraction)
            accum(gp0,1,(1,key))
            accum(gp0,-1,remap(key,{0:1,1:0}))
            gp = clean(gp0)
            for ckey,c in gp.items():
                accum(out,c,scalar_close(ckey,((0,2,0),(1,3,1)),dz=2))
                accum(out,c,scalar_close(ckey,((0,3,0),(1,2,1)),dz=2))
        for gkey,gc in gp.items():
            for grad,c in gradient(gkey,4).items():
                accum(out,gc*c,contract_G_with_X(grad))
            fact,qg = q_times(gkey,4)
            accum(out,gc*fact*(2*AEXP-1),contract_G_with_X(qg))
    return clean(out)


def pair_contraction(left, right, pairs):
    """Contract two tensors according to a matching on their labelled slots.

    Pair entries are ((side,index),(side,index)); side is 0 or 1. Distinct
    X vertices in the two inputs are renamed before contractions are taken.
    """
    maps = [{},{}]
    next_x = 7
    for side,key in enumerate((left,right)):
        present = sorted({v for e in key[4] for v in e[:2] if v in (7,8)})
        for vertex in present:
            maps[side][vertex] = next_x
            next_x += 1
    assert next_x <= 9
    for i,(a,b) in enumerate(pairs):
        assert a[1] not in maps[a[0]] and b[1] not in maps[b[0]]
        maps[a[0]][a[1]] = 100+i
        maps[b[0]][b[1]] = 100+i
    edges = []
    for side,key in enumerate((left,right)):
        mp = maps[side]
        edges += [(mp.get(u,u),mp.get(v,v),k) for u,v,k in key[4]]
    return build(left[0]+right[0],left[1]+right[1],left[2]+right[2],
                 left[3]+right[3],edges)


@lru_cache(None)
def projection_matchings(rank, kind):
    """Bilinear formulas derived algebraically from the printed projections."""
    recipes = []
    if kind == 'none':
        return ((1,tuple(((0,i),(1,i)) for i in range(rank))),)
    for perm in permutations(range(rank)):
        if kind == 'anti':
            inversions = sum(perm[i]>perm[j] for i in range(rank) for j in range(i+1,rank))
            c = (-1)**inversions
        elif kind == 'sym':
            c = 5 if rank==2 else 7
        elif kind == 'hook':
            assert rank == 3
            c = 16 if perm in ((0,1,2),(1,0,2)) else -8
        else:
            raise ValueError(kind)
        recipes.append((c,tuple(((0,i),(1,perm[i])) for i in range(rank))))
    if kind == 'sym' and rank == 2:
        recipes.append((-2,(((0,0),(0,1)),((1,0),(1,1)))))
    elif kind in ('sym','hook') and rank == 3:
        tracepairs = ((0,1),(0,2),(1,2))
        weights = (1,1,1) if kind == 'sym' else (2,-1,-1)
        for ia,(a,b) in enumerate(tracepairs):
            left_free = 3-a-b
            for ib,(c,d) in enumerate(tracepairs):
                right_free = 3-c-d
                recipes.append((-2*weights[ia]*weights[ib],
                                (((0,a),(0,b)),((1,c),(1,d)),
                                 ((0,left_free),(1,right_free)))))
    return tuple(recipes)


def projected_inner(left,right,rank,kind):
    out = defaultdict(Fraction)
    for c,pairs in projection_matchings(rank,kind):
        accum(out,c,pair_contraction(left,right,pairs))
    return clean(out)


def input_tables(path):
    # HARD BOUND: never read the optional code after the permitted prefix.
    with open(path) as f:
        lines = list(islice(f,1124))
    text = ''.join(lines)
    table1 = text.split('Table I:\n\n~~~\n',1)[1].split('\n~~~',1)[0]
    table2 = text.split('Table II:\n\n~~~\n',1)[1].split('\n~~~',1)[0]
    rows = []
    for line in table1.splitlines():
        name,code,coefficient = line.split()
        rows.append((name,parse_monomial(code,RANKS[name]),int(coefficient)))
    blocks = []
    for line in table2.splitlines():
        if line.startswith('@'):
            _,rank,kind,mode = line.split()
            blocks.append({'rank':int(rank),'kind':kind,'mode':mode,'rows':[]})
        else:
            entries = line.split()
            block = blocks[-1]
            if block['rank'] >= 0:
                block['rows'].append((parse_monomial(entries[0],block['rank']),
                                      tuple(map(int,entries[1:]))))
    return rows,[b for b in blocks if b['rank']>=0],text


def expand(rows,blocks):
    # Every running coefficient is scaled by Q^2, avoiding small denominators
    # after each complete Table-I row contribution has been added.
    result = defaultdict(Fraction)
    start = time.monotonic()
    for name,key,n in rows:
        for mon,c in row_interior(name,key).items():
            result[mon] -= n*Q*c
    print(f'Table I expanded: {len(clean(result))} keys; {time.monotonic()-start:.2f}s',flush=True)
    for bi,block in enumerate(blocks):
        rank,kind,mode = (block[x] for x in ('rank','kind','mode'))
        data = block['rows']
        for i,(earlier,ci) in enumerate(data):
            for j in range(i,len(data)):
                later,cj = data[j]
                assert len(ci)==len(cj)
                weight = sum(a*b for a,b in zip(ci,cj))*(1 if i==j else 2)
                if not weight:
                    continue
                for key,c in projected_inner(later,earlier,rank,kind).items():
                    result[key] += weight*c
                    if mode == 'B':
                        accum(result,-weight*c,remap(key,{},dh=2))
                        accum(result,-weight*c,remap(key,{},extra_edges=((5,5,0),)))
                    else:
                        assert mode == 'I'
        print(f'Block {bi+1}/{len(blocks)} rank={rank} {kind} {mode}: '
              f'{len(clean(result))} keys; {time.monotonic()-start:.2f}s',flush=True)
    # Magnitude allowances: (2/25)w²+(2/25)z²+(1/4)|ell|²+|X|².
    accum(result,Fraction(2,25)*Q**2,build(w=2))
    accum(result,Fraction(2,25)*Q**2,build(z=2))
    accum(result,Fraction(1,4)*Q**2,build(edges=((6,6,0),)))
    accum(result,Q**2,build(edges=((7,8,0),(7,8,0),(7,8,0))))
    result = clean(result)
    assert all(c.denominator == 1 for c in result.values())
    return {k:Fraction(c,Q**2) for k,c in result.items()}


def self_checks():
    # The elementary U=A identity is explicitly given in the mathematical text.
    row = row_interior('U',parse_monomial('000011',2))
    expected = defaultdict(Fraction)
    accum(expected,5,build(z=2))
    accum(expected,1,build(edges=((7,8,0),(7,8,0),(7,8,0))))
    accum(expected,2*AEXP-2,build(edges=((7,7,1),(8,8,1),(7,8,0))))
    assert row == clean(expected), (row,expected)
    assert build(traces=(0,1,2))[0] == 0
    assert build(traces=(0,2))[0] == 5
    assert build(edges=((7,7,0),(7,5,0)))[0] == 0
    # Symmetric A is annihilated by antisymmetrization, delta by STF projection.
    amat = parse_monomial('000011',2)
    delta = parse_monomial('000010',2)
    assert projected_inner(amat,amat,2,'anti') == {}
    assert projected_inner(delta,delta,2,'sym') == {}
    assert projected_inner(amat,amat,2,'sym') == {ZERO:10}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--input',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    args = parser.parse_args()
    self_checks()
    rows,blocks,prefix = input_tables(args.input)
    coefficients = expand(rows,blocks)
    from bounds import summarize
    summary = summarize(coefficients)
    summary['scope'] = 'Full finite interior expansion and exact magnitude bounds; no boundary expansion.'
    summary['input_prefix_sha256'] = hashlib.sha256(prefix.encode()).hexdigest()
    summary['table_I_rows'] = len(rows)
    summary['interior_blocks'] = len(blocks)
    summary['interior_rows'] = sum(len(b['rows']) for b in blocks)
    args.out.mkdir(parents=True,exist_ok=True)
    encoded = [{'key':[h,w,z,list(t),[list(e) for e in es]],
                'scaled_coefficient':int(c*Q**2)}
               for (h,w,z,t,es),c in sorted(coefficients.items())]
    (args.out/'coefficients.json').write_text(json.dumps(encoded,indent=2)+'\n')
    (args.out/'results.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k!='per_key'},indent=2),flush=True)


if __name__ == '__main__':
    main()
