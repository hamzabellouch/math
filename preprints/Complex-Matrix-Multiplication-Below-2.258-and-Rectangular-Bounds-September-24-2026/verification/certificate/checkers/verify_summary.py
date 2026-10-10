"""Exact final arithmetic and consistency checks for the local audit."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent.parent
HERE = ROOT / "local-check"
cert = json.loads((ROOT / "audit/chart-check/qP780_gmp.certificate.json").read_text())
epsilon = F(int(cert["residual_numerator_upper"]), int(cert["residual_denominator"]))
eta = F(2, 10**9)
debt = 6 * epsilon / eta
interior_margin = F(98, 10**9)
boundary_margin = F(55, 10**7)
inset_cost = F(13, 10**7)
assert epsilon < F(3329, 10**25)
assert debt < F(1, 10**12) < interior_margin
assert boundary_margin > inset_cost

# ln(3) = 2 atanh(1/2), with a rigorous geometric remainder.
terms = 100
ln3_lower = sum(F(2, (2*k+1) * 2**(2*k+1)) for k in range(terms))
ln3_upper = ln3_lower + F(2, (2*terms+1)*2**(2*terms+1)) / (1-F(1,4))
coefficients = [F(s) for s in (HERE / "newc22").read_text().split()]
assert len(coefficients) == 52
center_gap_lower = coefficients[0] - ln3_upper
assert center_gap_lower > F(7094, 10**9)

sectors = json.loads((HERE / "interior-final/results.json").read_text())
assert len(sectors) == 128 and all(x["exit_code"] == 0 for x in sectors)
assert (HERE / "hcheck.log").read_text().strip() == "h -4180063084"
assert (HERE / "bcheck.log").read_text().strip() == "b 0 65536 amb 6 terms 7250 edge 128315602072 cap 152568202355"
expected = {
    HERE / "qP": "7dc037ea127cece2216f3219eeeca4cdab0288319a10111a78d272586b776f0b",
    ROOT / "audit/chart-check/qP780_gmp": "f23c0480f1109509545fdd17bb4de81602f50952411554b337105defbe7a070c",
}
for path, digest in expected.items():
    assert hashlib.sha256(path.read_bytes()).hexdigest() == digest

def bound(value):
    return {"numerator": str(value.numerator), "denominator": str(value.denominator),
            "decimal_for_display": float(value)}
out = {"exact_summary_checks": "PASS", "beta": "1129/500",
       "scope": "Numerical checks and evidence consistency only; these checks do not verify the mathematical lemmas.",
       "epsilon_upper": bound(epsilon), "residual_debt_upper": bound(debt),
       "interior_margin_lower": bound(interior_margin),
       "boundary_margin_lower": bound(boundary_margin),
       "inset_cost_upper": bound(inset_cost),
       "center_gap_lower": bound(center_gap_lower),
       "local_interior_sectors_passed": len(sectors),
       "original_boundary_outputs_reproduced": True}
(HERE / "verification-summary.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps({key: value for key, value in out.items() if not isinstance(value, dict)}, indent=2))
print("center gap >", float(center_gap_lower), "residual debt <", float(debt))
