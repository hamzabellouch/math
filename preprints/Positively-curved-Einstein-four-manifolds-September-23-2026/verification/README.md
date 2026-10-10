# Exact arithmetic verification

Requires Python 3.10 or later and only the standard library. No network
connection or external data is required.

From this directory:

```sh
python -B verify.py --check
```

The command uses `verify.py`, `polynomial.py`, and `results.json`. It
recomputes the finite results and compares the complete output with
`results.json` without modifying it. Checks remain active under Python `-O`.
Success requires exit status 0, a `PASS` line, and
`"all_passed": true` in the printed summary.

## Other files

- `COVERAGE.md`: location and limits of the checked data.
- `dependencies.json`: runtime requirements.
- `manifest.json`: current file sizes and hashes.
- `portability_check.py` and `portability-results.json`: optional diagnostics.
