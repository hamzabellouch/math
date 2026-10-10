# Parameter verification

Requires Python 3.10 or later and `mpmath==1.3.0`. Run with assertions enabled; do not use `-O`, `-OO`, or `PYTHONOPTIMIZE`.

From the `verification/` directory:

```sh
python3 -m pip install -r data/requirements.txt
verification_output=$(mktemp -d)
python3 -B scripts/verify_parameters.py --mode interval --dps 80 --rational-log \
  --output "$verification_output/certificate-interval-series.json"
```

The verifier reads the hash-checked `data/parameters.json`; `data/certificate-interval-series.json` is the stored reference output. The TSV and other certificate JSON are supplementary files. Keep an explicit `--output` as above: omitting it replaces the packaged certificate.

The command must exit zero with every entry in `checks` true. The output's `scalars.strict_gap` encloses a positive margin for 2.371056, and `scalars.exponent_upper_bound` encloses the exponent ratio.

Only `--mode interval` produces certified enclosures; `--mode point` is diagnostic. This command verifies the finite parameter bound, not the mathematical extraction proof.
