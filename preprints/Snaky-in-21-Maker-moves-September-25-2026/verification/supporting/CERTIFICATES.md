# Finite-certificate verification

Requires Python 3.10 or later with only the standard library. The `route21/`, `route25/`, and `route35/` directories contain separate certificate encodings and their checkers; use each route's own checker.

From the `verification/` directory, run:

```sh
python3 supporting/verify_all.py --output-dir /absolute/path/to/check-output
```

Use a writable output directory. The command writes per-route results and `report.json` there. Success is exit status 0 and `status: PASS` in `report.json`.

The command verifies finite certificate reconstruction and local set identities. The manuscript supplies the strategy induction and arbitrary-ownership arguments.
