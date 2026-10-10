# Finite verification

Requires Python 3.11 or later with assertions enabled: do not use `-O`, `-OO`, or `PYTHONOPTIMIZE`. The scalar and trial programs use only the standard library; the thermal program also requires NumPy and SciPy.

Run from the article directory with a separate output directory:

```sh
article_dir="$PWD"
verification_output=$(mktemp -d)
python3 "$article_dir/verification/scalar_checks.py" "$verification_output"
python3 "$article_dir/verification/trial_verify.py" "$verification_output"
(cd "$verification_output" && python3 "$article_dir/verification/thermal_certificate_check.py")
```

The thermal program writes to its current directory, so keep the subshell above. Each command must exit zero and print its final success message.

| Program | Main output files in `$verification_output` | Final success message |
|---|---|---|
| `scalar_checks.py` | `scalar-certificate.json` | `PASS: 67 exact scalar comparisons and equalities; no floating-point premise` |
| `trial_verify.py` | `trial-exact-matrices.json`, `trial-exact-results.json` | `All four printed certificates and five independent physical-space comparisons passed.` |
| `thermal_certificate_check.py` | `thermal_certificate_results.json` | `All 15 exact recurrences and both thermal conclusions certified.` |

Compare the generated files with the stored certificates:

```sh
python3 - "$article_dir/verification" "$verification_output" <<'PYCOMPARE'
import json, sys
from pathlib import Path
stored, replay = map(Path, sys.argv[1:])
for name in ("trial-exact-matrices.json", "trial-exact-results.json",
             "trial-direct-physical-crosscheck.json"):
    if (stored / name).read_bytes() != (replay / name).read_bytes():
        raise SystemExit(f"Byte difference: {name}")
for name in ("scalar-certificate.json", "thermal_certificate_results.json"):
    a, b = (json.loads((root / name).read_text()) for root in (stored, replay))
    if name == "scalar-certificate.json":
        a.pop("wall_seconds"); b.pop("wall_seconds")
    else:
        print("Inspect recorded Python build strings:",
              a["toolchain"]["python"], b["toolchain"]["python"])
        for value in (a, b):
            value.pop("seconds")
            for case in value["cases"]:
                case.pop("seconds")
            value["toolchain"].pop("python")
    if json.dumps(a, sort_keys=True) != json.dumps(b, sort_keys=True):
        raise SystemExit(f"Certificate or unexpected metadata difference: {name}")
print("All certificate data match; only the listed metadata may differ.")
PYCOMPARE
```

The three trial files must match byte-for-byte. The only allowed JSON differences are scalar `wall_seconds` and thermal `seconds`, `cases[].seconds`, and `toolchain.python`; the Python build strings are printed for inspection. The comparison must exit zero and print its final success message.

The programs embed their finite inputs and do not read the stored JSON files as premises. They verify finite scalar, thermal, and trial calculations, not the analytic proof.
