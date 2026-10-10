# Scalar and segment verification

Requires Python 3 and SymPy 1.14.0, pinned in `requirements.txt`. Run with
assertions enabled: do not use `-O`, `-OO`, or `PYTHONOPTIMIZE`.

## Run

From this directory:

```sh
python3 -m pip install -r requirements.txt
python3 reproduce.py --output verification-results
```

The output directory must not exist. `reproduce.py` checks the program hashes
in `SOURCE-MANIFEST.json`, copies the ten programs from `programs/` into the
new directory, and runs them in dependency order. In particular,
`scalar_intervals.py` generates `scalar-samples.json` before
`segment-auxiliary-intervals.py` reads it.

## Program-to-claim index

| Program in `programs/` | Finite computation |
| --- | --- |
| `scalar_intervals.py` | Scalar node enclosures and interval sums |
| `scalar_algebra.py` | Scalar tail, interpolation, and pointwise bounds |
| `scalar_identities.py` | Profile differential identities |
| `scalar-analytic.py` | Constants for analytic strip bounds |
| `interpolation-check.py` | Interpolation remainders and chord factor |
| `segment-auxiliary-intervals.py` | Auxiliary segment sums and budgets |
| `segment-middle-polynomials.py` | Middle-width Bernstein polynomial bounds |
| `segment-middle-r-certificate.py` | Middle-width cubic bounds |
| `segment-large-check.py` | Larger-width interval bounds |
| `segment-large-tail-audit.py` | Larger-width tail bounds |

## Outputs and success

The selected directory contains the copied programs, generated data and JSON
reports, per-program `*.stdout.txt` and `*.stderr.txt` logs, and `RUN.json`.
Several programs report failures only in JSON, so use the runner instead of
treating an individual exit code as sufficient.

Success requires exit status 0 and `"passed": true` in `RUN.json`, with all ten
steps passed. `matches_saved_original_bytes` is an informational comparison,
not a success criterion.

These commands check the specified finite arithmetic. The manuscript supplies
the analytic and geometric arguments that use it.
