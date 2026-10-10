#!/usr/bin/env python3
"""Exact opposite-field trial certificates, reconstructed from the printed appendix.

Python standard library only.  Run with an optional output directory:
    python3 trial_verify.py [OUTPUT_DIRECTORY]
This is a fresh transcription of the mathematical specification, not recovery
of an original supporting program.  No eigensolver or floating-point premise
is used.  Large certificate integers are serialized as decimal strings.
"""

import hashlib
import itertools
import json
from pathlib import Path
import platform
import sys
import time


if not __debug__:
    raise SystemExit("Run without Python optimization (-O/-OO or PYTHONOPTIMIZE): exact certificate assertions are required.")


ELLS = (1, 1, 1, 1, 3, 3, 3, 5)
DIAGONALS = (-289, -84, -9, 33, -22, 27, 71, -11)
BETAS = (10000, 5620, 2456, 4868, 82, -809, 12475, -9645)
KAPPAS = (12, 12, 12, 12, 6, 6, 6, 1)
COUPLINGS = {
    (1, 5): -11, (1, 6): -35, (1, 7): -28,
    (2, 5): -23, (2, 6): 16, (2, 7): -49,
    (3, 5): -6, (3, 6): -25, (3, 7): -20,
    (4, 5): -34, (4, 6): 9, (4, 7): -32,
    (5, 8): 1, (6, 8): 2, (7, 8): -16,
}
PRINTED = {
    34: (202, 715867, 4031974),
    78: (440, 747265, 4041175),
    142: (787, 121288, 4041110),
    240: (1317, 165352, 4041006),
}


def sparse(matrix):
    return [[(j, value) for j, value in enumerate(row) if value]
            for row in matrix]


def row_times(row, matrix_sparse):
    result = [0] * len(row)
    for i, value in enumerate(row):
        if value:
            for j, coefficient in matrix_sparse[i]:
                result[j] += value * coefficient
    return result


def matrix_product(left, right):
    right_sparse = sparse(right)
    return [row_times(row, right_sparse) for row in left]


def dot(left, right):
    return sum(a * b for a, b in zip(left, right))


def construct():
    labels = [(i, d) for i, ell in enumerate(ELLS, 1)
              for d in range(-ell, ell + 1, 2)]
    assert len(labels) == 26
    tensors = {}
    for s in (-1, 0, 1):
        matrix = []
        for i, d in labels:
            ell = ELLS[i - 1]
            r = (ell + d) // 2
            row = []
            for j, e in labels:
                k = ELLS[j - 1]
                if e != d + 2 * s or abs(k - ell) > 2 or (k == ell and i != j):
                    value = 0
                elif k == ell + 2:
                    factors = (2 * (ell + 1 - r) * (ell + 2 - r),
                               2 * (r + 1) * (ell - r + 1),
                               (r + 1) * (r + 2))
                    value = COUPLINGS[i, j] * factors[s + 1]
                elif k == ell:
                    value = DIAGONALS[i - 1] * (2 * (ell - r + 1), d, -(r + 1))[s + 1]
                else:
                    assert k == ell - 2
                    value = -COUPLINGS[j, i] * (2, -2, 1)[s + 1]
                row.append(value)
            matrix.append(row)
        tensors[s] = matrix
    left = [BETAS[i - 1] if d == -1 else 0 for i, d in labels]
    right = [KAPPAS[i - 1] * BETAS[i - 1] if d == -1 else 0
             for i, d in labels]
    pairs = [(a, b) for a in range(26) for b in range(26)
             if labels[a][1] == labels[b][1]]
    assert len(pairs) == 162
    products = {(s, t): matrix_product(tensors[s], tensors[t])
                for s in (-1, 0, 1) for t in (-1, 0, 1)}

    # These entrywise checks verify the weight-change premise of the exact
    # invariant-subspace proof.  They cover full 26-dimensional tensors, not
    # only their restricted products.
    for s, matrix in tensors.items():
        for a, row in enumerate(matrix):
            for b, value in enumerate(row):
                assert not value or labels[b][1] - labels[a][1] == 2 * s
    for (s, t), matrix in products.items():
        for a, row in enumerate(matrix):
            for b, value in enumerate(row):
                assert not value or labels[b][1] - labels[a][1] == 2 * (s + t)

    transfer, field, bond = [], [], []
    for a, b in pairs:
        trow, grow, orow = [], [], []
        for c, d in pairs:
            trow.append(sum(tensors[s][a][c] * tensors[s][b][d]
                            for s in (-1, 0, 1)))
            grow.append(sum(s * tensors[s][a][c] * tensors[s][b][d]
                            for s in (-1, 0, 1)))
            value = sum(s * t * products[s, t][a][c] * products[s, t][b][d]
                        for s in (-1, 0, 1) for t in (-1, 0, 1))
            for s in (-1, 0):
                for t in (0, 1):
                    one, two = products[s, t], products[s + 1, t - 1]
                    value += one[a][c] * two[b][d] + two[a][c] * one[b][d]
            orow.append(value)
        transfer.append(trow)
        field.append(grow)
        bond.append(orow)
    lzero = [left[a] * left[b] for a, b in pairs]
    u = [right[a] * right[b] for a, b in pairs]
    return labels, tensors, left, right, pairs, transfer, field, bond, lzero, u


def direct_physical(tensors, left, right, m):
    """Enumerate physical words and apply the ordinary spin-one Hamiltonian.

    This contraction does not use T, G, O, paired labels, or the row
    recurrence.  Physical raising/lowering gives unit bond coefficients.
    """
    tensor_sparse = {s: sparse(matrix) for s, matrix in tensors.items()}
    states = {(): left}
    for _ in range(m):
        states = {word + (s,): row_times(row, tensor_sparse[s])
                  for word, row in states.items() for s in (-1, 0, 1)}
    amplitudes = {word: dot(row, right) for word, row in states.items()}
    assert all(not amplitude or sum(word) == 0 for word, amplitude in amplitudes.items())
    norm = sum(amplitude * amplitude for amplitude in amplitudes.values())
    bulk = left_field = right_field = 0
    for word, amplitude in amplitudes.items():
        left_field += word[0] * amplitude * amplitude
        right_field += word[-1] * amplitude * amplitude
        for j in range(m - 1):
            bulk += word[j] * word[j + 1] * amplitude * amplitude
            for step in (-1, 1):
                new_left, new_right = word[j] + step, word[j + 1] - step
                if -1 <= new_left <= 1 and -1 <= new_right <= 1:
                    other = word[:j] + (new_left, new_right) + word[j + 2:]
                    bulk += amplitude * amplitudes[other]
    shifted = 500000 * bulk - 300000 * left_field + 300000 * right_field + 700741 * m * norm
    return {
        "physical_words": len(amplitudes),
        "nonzero_amplitudes": sum(value != 0 for value in amplitudes.values()),
        "V": str(norm), "bulk_numerator": str(bulk),
        "left_Sz_numerator": str(left_field), "right_Sz_numerator": str(right_field),
        "H_star": str(shifted),
    }


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def main():
    started = time.time()
    output = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent
    output.mkdir(parents=True, exist_ok=True)
    labels, tensors, left, right, pairs, transfer, field, bond, lzero, u = construct()
    write_json(output / "trial-exact-matrices.json", {
        "virtual_labels": labels, "A": tensors, "b": left, "c": right,
        "restricted_pair_indices_zero_based": pairs,
        "restricted_pair_labels": [[labels[a], labels[b]] for a, b in pairs],
        "T_star": transfer, "G_star": field, "O_star": bond,
        "L_0": lzero, "u": u,
    })
    tsp, gsp, osp = map(sparse, (transfer, field, bond))
    gu = [dot(row, u) for row in field]
    x = lzero
    y = row_times(lzero, tsp)
    w = [-300000 * value for value in row_times(lzero, gsp)]
    records, direct_records, all_matched = {}, {}, True
    for m in range(2, 241):
        new_y = row_times(y, tsp)
        wt, xo = row_times(w, tsp), row_times(x, osp)
        # x T = y by the row invariant, hence (x T) T = new_y.
        new_w = [a + 500000 * b + 700741 * c
                 for a, b, c in zip(wt, xo, new_y)]
        x, y, w = y, new_y, new_w
        if m <= 6 or m in PRINTED:
            norm = dot(y, u)
            shifted = dot(w, u) + 300000 * dot(x, gu) + 700741 * norm
            if m <= 6:
                direct = direct_physical(tensors, left, right, m)
                direct["matches_transfer_norm"] = int(direct["V"]) == norm
                direct["matches_transfer_shifted_energy"] = int(direct["H_star"]) == shifted
                assert direct["matches_transfer_norm"] and direct["matches_transfer_shifted_energy"]
                direct_records[m] = direct
            if m in PRINTED:
                assert norm > 0
                digits = len(str(norm))
                leading = norm // 10 ** (digits - 6)
                energy_floor = (20 * shifted) // norm
                assert 10 ** (digits - 1) <= norm < 10 ** digits
                assert leading * 10 ** (digits - 6) <= norm < (leading + 1) * 10 ** (digits - 6)
                assert energy_floor * norm <= 20 * shifted < (energy_floor + 1) * norm
                margin = 202100 * norm - shifted
                got = digits, leading, energy_floor
                matched = got == PRINTED[m]
                all_matched = all_matched and matched and margin > 0
                records[m] = {
                    "V_m": str(norm), "H_m_star": str(shifted),
                    "strict_margin_202100V_minus_H": str(margin),
                    "digits": digits, "leading_six": leading,
                    "energy_floor_times_10000000": energy_floor,
                    "printed": PRINTED[m], "matches_printed": matched,
                    "strict_margin_positive": margin > 0,
                }
                print(f"m={m}: p={digits}, q={leading}, k={energy_floor}; "
                      f"matches_printed={matched}; strict_margin_positive={margin > 0}", flush=True)
    write_json(output / "trial-exact-results.json", records)
    write_json(output / "trial-direct-physical-crosscheck.json", direct_records)
    files = ("trial-exact-matrices.json", "trial-exact-results.json", "trial-direct-physical-crosscheck.json")
    write_json(output / "trial-run-record.json", {
        "provenance": "Fresh reconstruction from the printed appendix, not an original recovered helper.",
        "python": sys.version, "implementation": platform.python_implementation(),
        "platform": platform.platform(), "elapsed_seconds": time.time() - started,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "command": [sys.executable, str(Path(__file__).resolve()), str(output.resolve())],
        "all_four_certificates_match": all_matched,
        "direct_physical_lengths": list(direct_records),
        "weight_difference_invariance_entrywise_premises_checked": True,
        "virtual_dimension": len(labels), "restricted_dimension": len(pairs),
        "nonzero_entries": {name: sum(value != 0 for row in matrix for value in row)
                            for name, matrix in (("T_star", transfer), ("G_star", field), ("O_star", bond))},
        "artifacts": {name: {"sha256": hashlib.sha256((output / name).read_bytes()).hexdigest(),
                             "bytes": (output / name).stat().st_size} for name in files},
    })
    if not all_matched:
        raise SystemExit("Reconstructed certificate does not match printed claim; inspect exact output.")
    print("All four printed certificates and five independent physical-space comparisons passed.")


if __name__ == "__main__":
    main()
