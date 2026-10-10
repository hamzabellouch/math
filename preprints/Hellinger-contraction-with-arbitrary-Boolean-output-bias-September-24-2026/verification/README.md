# Exact arithmetic verification

Requires Python 3.9 or later with SymPy 1.14.0, plus a C++ compiler supporting
signed `__int128` and C++17, such as GCC or Clang. Keep Python assertions
enabled: do not use `-O`, `-OO`, or `PYTHONOPTIMIZE`.

## Run

From this directory:

```sh
python3 -m pip install -r requirements.txt
python3 verify_all.py --output-dir verification-results
```

The output directory must be new or empty. Omitting `--output-dir` creates a
uniquely named directory in the current working directory. The runner uses
`CXX` or `c++` by default; use `--cxx clang++` to select another compiler.
It compiles in temporary storage and runs all checks with isolated Python
interpreters.

## Files

- `interval_certificate.cpp` and `profile_certificate.py`: finite scalar and
  profile certificates.
- `central_band.py`, `intermediate_bias.py`, and `large_bias.py`: exact checks
  for the three bias ranges.
- `profile_formula_audit.py`: formula and table check using
  `data/profile_tables.txt`.
- `verify_all.py`: runner; `requirements.txt` pins SymPy.
- `provenance.json`: source and table metadata recorded with each run.

## Outputs and success

The selected directory receives `verification.json`, per-step stdout/stderr
logs, and `profile_formula_audit.results.json`. Success requires exit status 0,
a final `PASS`, and `"status": "pass"` in `verification.json`. On failure,
inspect the corresponding logs.

These commands check finite arithmetic. The manuscript supplies the analytic
argument connecting it to the theorem.
