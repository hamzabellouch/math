# Packing certificate verification

Requires Python 3 and `python-flint==0.9.0`. Run with assertions enabled; do not use `-O`, `-OO`, or `PYTHONOPTIMIZE`.

From the article directory:

```sh
python3 -m pip install -r verification/requirements.txt
python3 -B verification/verify_all.py
```

Keep `verification/data/certificate-inputs.json`, the three TSV tables in `verification/data/`, and the corresponding TeX tables in `build/data/` together. The verifier checks their identities and writes `finite.json`, `scalar.json`, and `summary.json` under `verification/results/`.

Success is a zero exit with `"status": "pass"` in the printed summary. A failed run may leave older or partial result files; those files do not establish success for that run.

The main command checks the finite matrix, residual, Bernstein, and scalar comparisons. The analytic quadrature, continuum, and infinite-tail arguments remain in the article.
