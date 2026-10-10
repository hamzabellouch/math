# Exact finite spectral selection

This optional check performs exact integer spectral-selection comparisons for
ambient dimension `n=16` and cutoff `k=50000`. It does not construct the metric
or verify the complete counterexample.

Requires Python 3 and its standard library, with assertions enabled. From the
paper directory, run:

```sh
env -u PYTHONOPTIMIZE python3 verification/counting-check.py
```

Do not use Python's `-O` or `-OO` options. Success is exit status zero with a
selected total strictly larger than the Euclidean comparator. Results are printed
to standard output; no files are written. `counting-check-output.txt` is a
reference output. The displayed ratio and elapsed time are informational.
