# Rectangular verification package

The `checks/` directory contains these inputs and programs:

| Path | Purpose |
| --- | --- |
| `verify_rational.py` | Exact rational bounds for the numerical witnesses |
| `verify_construction.py` | Finite-support and integer-count checks |
| `baseline_data.json` | Version-pinned public table inputs |
| `verify_baseline.py` | Exact comparisons using `baseline_data.json` |
| `run_checks.py` | Runs the selected checks and records script/data/output hashes |

Matching `.json` files are saved reference outputs. Use the fresh-copy commands in [`checks/README.md`](checks/README.md), because the programs write results beside their inputs.

These programs check finite arithmetic. The manuscript supplies the structural tensor, entropy, and closure arguments.
