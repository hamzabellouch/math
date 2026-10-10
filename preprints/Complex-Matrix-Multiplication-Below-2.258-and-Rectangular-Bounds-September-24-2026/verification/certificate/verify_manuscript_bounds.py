#!/usr/bin/env python3
"""Check the new manuscript's exact numerical interfaces after reproduce.py.

This standard-library postprocessor makes no network requests. It does not
replace the manuscript's proofs of analytic error or tensor/control lemmas.
It reads a completed reproduction directory and writes one new JSON report.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re

PACKAGE = Path(__file__).resolve().parent
EXPECTED_CHARTS = {
    "qP420_gmp": "7dc037ea127cece2216f3219eeeca4cdab0288319a10111a78d272586b776f0b",
    "qP780_gmp": "f23c0480f1109509545fdd17bb4de81602f50952411554b337105defbe7a070c",
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, explanation):
    if not condition:
        raise ValueError(explanation)


def rational(value):
    return {"numerator": str(value.numerator), "denominator": str(value.denominator),
            "decimal_for_display": float(value)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", type=Path, required=True,
                        help="Completed directory created by reproduce.py")
    parser.add_argument("--output", type=Path,
                        help="New report path; default: WORK/manuscript-bounds.json")
    args = parser.parse_args()
    work = args.work_dir.resolve()
    output = args.output or work / "manuscript-bounds.json"
    require(not output.exists(), "The report path already exists; choose a new --output")
    manifest = json.loads((PACKAGE / "package-manifest.json").read_text())
    for entry in manifest["files"]:
        path = PACKAGE / entry["path"]
        require(path.is_file() and path.stat().st_size == entry["bytes"] and
                digest(path) == entry["sha256"], "Package hash/size mismatch: " + entry["path"])
    provenance = json.loads((work / "driver-provenance.json").read_text())
    commands = provenance["commands"]
    require(all(row.get("exit_code") == 0 for row in commands),
            "At least one driver command did not finish successfully")
    required_stages = {"compiler-platform-preflight", "norms-qP420_gmp", "norms-qP780_gmp",
                       "compile-tensor-primitives", "tensor-primitives", "compile-hcheck",
                       "compile-bcheck", "generate-boundary-data", "hcheck", "bcheck",
                       "interior-final", "geometry", "exact-chart-certificate",
                       "recorded-bounds", "summary"}
    if not provenance["reuse_charts"]:
        required_stages |= {"compile-chart", "generate-qP420_gmp", "generate-qP780_gmp"}
    require(required_stages <= {row["stage"] for row in commands}, "Incomplete driver stages")
    for name, expected in EXPECTED_CHARTS.items():
        require(digest(work / "audit/chart-check" / name) == expected, "Chart hash mismatch")
    require(digest(work / "local-check/qP") == EXPECTED_CHARTS["qP420_gmp"],
            "Boundary reference chart mismatch")
    require(digest(work / "local-check/newc22") == digest(PACKAGE / "inputs/newc22"),
            "Barrier coefficient mismatch")

    htext = (work / "local-check/hcheck.log").read_text().strip()
    hmatch = re.fullmatch(r"h (-?\d+)", htext)
    require(hmatch is not None, "Unexpected H-check output")
    hgap = Fraction(int(hmatch[1]), 1 << 52)
    require(hgap > -Fraction(5, 10**6), "H-check threshold failed")
    btext = (work / "local-check/bcheck.log").read_text().strip()
    bmatch = re.fullmatch(r"b 0 65536 amb (\d+) terms (\d+) edge (-?\d+) cap (-?\d+)", btext)
    require(bmatch is not None, "Full boundary run is required")
    ambiguous, terms, edge_integer, cap_integer = map(int, bmatch.groups())
    require(ambiguous == 6 and terms == 7250, "Unexpected boundary coverage/data")
    edge = Fraction(edge_integer, 1 << 52)
    cap = Fraction(cap_integer, 1 << 52)
    require(edge > Fraction(2849, 10**8), "Repaired ledger needs actual edge gap > 28.49e-6")
    require(cap > Fraction(3387, 10**8), "Cap gap is below the reproduced reference bound")
    edge_after_two_allowances = edge - Fraction(10, 10**6) - Fraction(2, 10**6)
    require(edge_after_two_allowances > Fraction(1649, 10**8),
            "Edge gap does not pay the two stated conservative allowances")

    # These costs are proved analytically in the manuscript; this code only
    # performs the exact subtraction and checks the common surviving margin.
    boundary_ledger = {
        "full_face": edge_after_two_allowances,
        "transition_face": edge - Fraction(10, 10**6) - Fraction(65, 10**7),
        "full_cap": Fraction(8, 10**6) - Fraction(2, 10**7) - Fraction(4, 10**7),
        "transition_cap": Fraction(8, 10**6) - Fraction(24, 10**7),
    }
    boundary_margin = Fraction(55, 10**7)
    require(all(value > boundary_margin for value in boundary_ledger.values()),
            "The analytic allowances leave insufficient boundary margin")

    rows = json.loads((work / "local-check/interior-final/results.json").read_text())
    require(len(rows) == 128 and sorted(row["sector"] for row in rows) == list(range(128)),
            "Interior sector identifiers are incomplete or duplicated")
    reference = json.loads((PACKAGE / "certificates/interior-sectors.json").read_text())
    expected = {row["sector"]: row["sha256"] for row in reference}
    for row in rows:
        data_path = work / "local-check/interior-final/cells" / f"{row['sector']:03d}.dat"
        require(row["exit_code"] == 0 and digest(data_path) == row["sha256"] == expected[row["sector"]],
                "Interior exit code or sector-input hash mismatch")

    cert = json.loads((work / "audit/chart-check/qP780_gmp.certificate.json").read_text())
    epsilon = Fraction(int(cert["residual_numerator_upper"]), int(cert["residual_denominator"]))
    debt = 6 * epsilon / Fraction(2, 10**9)
    require(epsilon < Fraction(3329, 10**25), "Residual bound failed")
    require(debt < Fraction(1, 10**12), "Residual-debt bound failed")
    coefficients = [Fraction(x) for x in (PACKAGE / "inputs/newc22").read_text().split()]
    indices = [(i+j, i-j) for i in range(23) for j in range(i % 3, min(i, 22-i)+1, 3)]
    require(len(coefficients) == len(indices) == 52, "Expected all 52 barrier coefficients")
    radius = Fraction(31, 25)
    fourth = sum(abs(c) * radius**(d-4) * d*(d-1)*(d-2)*(d-3)
                 for c, (d, _) in zip(coefficients, indices))
    require(fourth < 435000000, "Physical fourth-derivative coefficient bound failed")
    nterms = 100
    ln3_lower = sum(Fraction(2, (2*k+1)*2**(2*k+1)) for k in range(nterms))
    ln3_upper = ln3_lower + Fraction(2, (2*nterms+1)*2**(2*nterms+1)) / Fraction(3, 4)
    gap = coefficients[0] - ln3_upper
    require(gap > Fraction(70946, 10**10), "Center gap must exceed 7.0946e-6")
    result = {
        "format_version": 1, "checks": "PASS", "beta": "1129/500",
        "scope": "Exact finite numerical interfaces; analytic bounds and tensor/control arguments are proved in the manuscript.",
        "chart_recurrence_regeneration_in_this_run": not provenance["reuse_charts"],
        "reuse_charts_note": "When charts are reused, this postcheck verifies their hashes, not their recurrences. Run without --reuse-charts to regenerate both charts.",
        "full_boundary_intervals": 65536, "ambiguous_intervals": ambiguous,
        "transition_subcells_per_ambiguous_interval": 8192,
        "interior_sectors": len(rows), "all_saved_sector_data_hashes_match_reference": True,
        "h_sample_minimum": rational(hgap), "edge_sample_minimum": rational(edge),
        "cap_sample_minimum": rational(cap),
        "edge_after_10e_minus6_and_2e_minus6_allowances": rational(edge_after_two_allowances),
        "boundary_arithmetic_given_manuscript_allowances": {key: rational(value) for key, value in boundary_ledger.items()},
        "common_boundary_margin_lower": rational(boundary_margin),
        "epsilon_upper": rational(epsilon), "residual_debt_upper": rational(debt),
        "phi_fourth_derivative_coefficient_bound": rational(fourth),
        "center_gap_lower": rational(gap),
        "analytic_premises_not_proved_by_this_program": [
            "The tensor restrictions, bank conventions, compilation and adaptive-process lower-test principles.",
            "Fixed-point, truncation, interpolation and boundary displacement estimates.",
            "The global interior margin 9.8e-8, boundary margin 5.5e-6, and inset cost 1.3e-6.",
            "The asymptotic sum inequality and extraction of a strict exponent bound."
        ],
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("x") as stream:
        json.dump(result, stream, indent=2)
        stream.write("\n")
    print("PASS: exact manuscript bounds; complete sector identities/hashes; full boundary range.")
    print("Output:", output)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        raise SystemExit("Verification failed: " + str(error))
