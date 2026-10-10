"""Check the two exact energy windows for the single polynomial matrix triple."""
import json
from pathlib import Path

if not __debug__:
    raise SystemExit("Assertions must be enabled.")

root = Path(__file__).resolve().parent
for length, c in ((72, 1401482112601), (120, 1401482105174)):
    data = json.loads((root/f"certificate{length}.json").read_text())
    num = int(next(data[k] for k in ("num", "one_bond_energy_numerator", "U") if k in data))
    norm = int(next(data[k] for k in ("norm", "V") if k in data))
    assert data["length"] == length and norm > 0
    assert -c*norm <= 10**12*num < (1-c)*norm
    assert 1-c < -1401482000000
    assert -700741*norm-500000*num > 0
    print(length, "positive norm; exact interval and variational margin passed")
