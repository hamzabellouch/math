#!/usr/bin/env python3
"""Post-freeze comparison only; not a dependency of engine.py.

This adapter reads the old result JSON, never the implementation producing it.
The engine and its first outputs were frozen before this adapter was authored.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from engine import canonical


def key_of(raw):
    h,w,z,traces,edges = raw
    return (h,w,z,tuple(traces),tuple(tuple(e) for e in edges))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--oracle',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    args = ap.parse_args()
    ours = json.loads((args.output/'results.json').read_text())
    oracle_bytes = args.oracle.read_bytes()
    old = json.loads(oracle_bytes)
    actual = {key_of(item['key']):item for item in ours['per_key']}
    old_to_new = {-1:5,-2:6,-3:7,-4:8}
    reference = {}
    for item in old['all_interior_keys']:
        rank,h,w,z,traces,edges = item['term']
        assert rank == 0
        mapped = tuple((old_to_new[u],old_to_new[v],k) for u,v,k in edges)
        factor,key = canonical((h,w,z,tuple(traces),mapped))
        assert factor == 1 and key not in reference
        reference[key] = item
    missing = list(reference.keys()-actual.keys())
    extra = list(actual.keys()-reference.keys())
    coefficient_mismatches, pair_mismatches, rounding_mismatches = [],[],[]
    for key in actual.keys() & reference.keys():
        a,b = actual[key],reference[key]
        c = Fraction(a['coefficient']['numerator'],a['coefficient']['denominator'])
        if c != Fraction(b['coefficient']):
            coefficient_mismatches.append(key)
        if a['pair'] != b['pair']:
            pair_mismatches.append(key)
        if Fraction(a['integerceil'],100000) != Fraction(b['root_upper']):
            rounding_mismatches.append(key)
    counts_equal = [x['count'] for x in ours['pairs']] == old['counts']
    entries_equal = [x['scaled_entry'] for x in ours['pairs']] == list(map(int,old['scaled_entries']))
    passed = counts_equal and entries_equal and not any((missing,extra,
                   coefficient_mismatches,pair_mismatches,rounding_mismatches))
    report = {
        'comparison_stage':'after frozen implementation and successful independent expansion',
        'oracle_path':str(args.oracle.resolve()),
        'oracle_sha256':hashlib.sha256(oracle_bytes).hexdigest(),
        'oracle_implementation_read':False,
        'our_key_count':len(actual),'oracle_key_count':len(reference),
        'missing_keys':len(missing),'extra_keys':len(extra),
        'coefficient_mismatches':len(coefficient_mismatches),
        'magnitude_pair_mismatches':len(pair_mismatches),
        'rounded_bound_mismatches':len(rounding_mismatches),
        'all_ten_counts_equal':counts_equal,'all_ten_scaled_entries_equal':entries_equal,
        'passed':passed,
    }
    (args.output/'oracle-comparison.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    assert passed


if __name__ == '__main__':
    main()
