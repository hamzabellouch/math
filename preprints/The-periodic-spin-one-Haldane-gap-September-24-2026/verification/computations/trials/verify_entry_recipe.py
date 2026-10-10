"""Check every entry of the paper's single polynomial matrix triple."""
from pathlib import Path
import hashlib
import json

if not __debug__:
    raise SystemExit("Assertions must be enabled.")

root = Path(__file__).resolve().parent
data_path = root / "matrix-data.json"
data = json.loads(data_path.read_text())
degrees = [1, 1, 1, 1, 3, 3, 3, 5]
labels = [(a, d) for a, ell in enumerate(degrees) for d in range(-ell, ell+1, 2)]
diagonal = [-289, -84, -9, 33, -22, 27, 71, -11]
pairs = [(a, b) for a, ell in enumerate(degrees) for b, k in enumerate(degrees) if k == ell+2]
off = dict(zip(pairs, [-11, -35, -28, -23, 16, -49, -6, -25, -20, -34, 9, -32, 1, 2, -16]))
assert [row[-1] for row in data["labels"]] == [d for a, d in labels]


def entry(s, row, column):
    a, d = row
    b, e = column
    ell, k = degrees[a], degrees[b]
    if e != d+2*s or abs(k-ell) > 2 or (k == ell and a != b):
        return 0
    r = (d+ell)//2
    if k == ell+2:
        coefficient = off[a, b]
        factor = [2*(ell+1-r)*(ell+2-r), 2*(r+1)*(ell-r+1), (r+1)*(r+2)][s+1]
    elif k == ell:
        coefficient = diagonal[a]
        factor = [2*(ell-r+1), d, -(r+1)][s+1]
    else:
        coefficient = -off[b, a]
        factor = [2, -2, 1][s+1]
    return coefficient*factor


count = 0
for s in (-1, 0, 1):
    for i, row in enumerate(labels):
        for j, column in enumerate(labels):
            assert entry(s, row, column) == data["matrices"][str(s)][i][j], (s, i, j)
            count += 1
record = {"entries_checked": count, "matrix_data_sha256": hashlib.sha256(data_path.read_bytes()).hexdigest(),
          "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(root/"entry-recipe-verification.json").write_text(json.dumps(record, indent=2)+"\n")
print(json.dumps(record, indent=2))
