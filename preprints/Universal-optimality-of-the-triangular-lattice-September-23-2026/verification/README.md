# Numerical verification

## Files and requirements

- `numeric_balls.py` checks the finite matrix, Bernstein, and tail inequalities.
- `arithmetic_bounds.py` checks the scalar error and tail bounds.
- `inputs.py` validates the source binding in `CERTIFICATE-INPUTS.json`.
- `requirements.txt` pins `python-flint==0.9.0`.

Use Python 3 with the pinned dependency. Do not use `-O`, `-OO`, or
`PYTHONOPTIMIZE`; the scalar verifier requires assertions. Keep this directory
inside the complete paper source tree: the manifest requires the listed
`build/` sources and checker files with their recorded sizes and hashes.
Input and output paths must not contain parent traversal or symlink components.

## Run

From the paper directory, using a fresh virtual environment and output path:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r verification/requirements.txt
.venv/bin/python -B verification/numeric_balls.py --output-dir build/verification-run
.venv/bin/python -B verification/arithmetic_bounds.py --output-dir build/verification-run
```

The programs create the output directory if needed and refuse existing files
with their output names. They may share one fresh directory because their
filenames differ. Without `--output-dir`, the default is `build/verification`
under the paper root. The supported interface is the command line.

## Outputs and success

`numeric_balls.py` writes `numeric_balls_results.json` and
`numeric_balls_run.log`. `arithmetic_bounds.py` writes
`arithmetic_bounds.json` and `arithmetic_bounds.log`.

A completed run requires exit status 0 and the corresponding complete success
JSON. The numerical result records `completed_counts` of 37,310 Bernstein
comparisons and ten tail comparisons; the scalar result records that all scalar
assertions were certified. On failure or interruption, inspect the log and use a
new output path before retrying; file presence alone is not success.

These commands check finite arithmetic, not the manuscript's analytic
reductions. They do not execute the separate floor-rounded matrix construction.
