# Finite verification

Run commands from `verification/`, the directory containing `verify.py`.

## Prerequisites

Use Python 3 with NumPy and SciPy. The tested environment is Python 3.12.13, NumPy 2.3.5, and SciPy 1.16.2 on x86-64 Linux.

```sh
python3 -m pip install numpy==2.3.5 scipy==1.16.2
```

Assertions must be enabled: do not use `-O` or `-OO`; leave `PYTHONOPTIMIZE` unset or set it to `0`. Verification requires no GPU or network access. The `--workers` option controls the source1 worker count and must be positive; use `--workers 1` to reduce concurrent memory use.

## Run the verifier

```sh
python3 verify.py
```

The default `all` selection recomputes 27 thermal cases, the 72-site and 120-site trial contractions, and the exact scalar checks. It writes to a new `build/verification/` directory under `verification/`. The output directory must not already exist and must be outside `computations/`. To choose another output directory or worker count:

```sh
python3 verify.py --output /tmp/haldane-verification --workers 8
```

The entry point checks the manifest bindings, copies required files to the output directory, and compares the computed full integers and rational interval endpoints with the retained certificates. Success means exit status zero, a final `PASS` message, and `verification.json` containing `"success": true`. Command logs are in the output directory's `logs/` subdirectory.

## Layout

- `source1/` and `source2/`: thermal calculations, reference totals, and supporting checks.
- `trials/`: 72-site and 120-site trial contractions and matrix-entry checks.
- `scalars/`: exact rational initialization and bootstrap checks.
- `evidence/`: retained expected certificates and supplementary results.
- `source-manifest.json`: file lists and integrity bindings used by `verify.py`.

Keep these files together under `computations/`. The scripts verify the finite inequalities; the transfer and uniform-gap arguments are given in the manuscript.
