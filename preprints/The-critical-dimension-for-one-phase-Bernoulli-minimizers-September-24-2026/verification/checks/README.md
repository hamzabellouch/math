# Finite-certificate checks

Run the command from the article directory with Python 3.10 or later. The full run requires a little-endian POSIX system, NumPy installed in that interpreter's environment (not only its user site), and a writable temporary directory. No network access is required.

```sh
python3 -B verification/checks/reproduce.py
```

The runner authenticates `verification/checks/original/certificate-inputs.txt` and the retained verifier files, checks both tables in `build/appendices/tables.tex`, and compares fresh finite-arithmetic results with the retained outputs. It works in temporary copies and leaves these files unchanged. Success is exit status 0 with all checks reporting `PASS`; a failed check exits nonzero.

The retained result files are historical. For results that record input or checker hashes, the runner validates those fields against the current authenticated files and requires every other byte to match the retained result. The retained oracle-comparison path is explicitly marked redacted; the runner separately validates the fresh path and compares every other field.

This command verifies finite algebra and coefficient comparisons, not the analytic reduction, the correspondence between mathematical formulas and code, or the whole proof.
