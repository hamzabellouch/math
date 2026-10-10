# [The critical dimension for one-phase Bernoulli minimizers](The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026.pdf)

**Author:** OpenAI

**Date:** September 24, 2026

## Citation

```bibtex
@misc{OAI:The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026,
  author = {{OpenAI}},
  title = {{The critical dimension for one-phase Bernoulli minimizers}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026/The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026.pdf}{OAI:The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026}},
  year = {2026}
}
```

## Verification

Use Python 3.10 or later on a little-endian POSIX system, with NumPy installed
in that interpreter. From this paper directory, run the complete exact
finite-certificate reproduction:

```sh
python3 -B verification/checks/reproduce.py
```

Success ends with `PASS both full interior engines and all supporting checks`.
For a bounded check of the pinned inputs and typeset tables without executing
the arithmetic engines, run:

```sh
python3 -B verification/checks/reproduce.py --verify-inputs-only
```

The existing integrity guard tests and deterministic appendix check are:

```sh
python3 -B verification/checks/test_reproduce.py
python3 -B verification/checks/generate_tables.py
```

The finite checks verify the supplied exact arithmetic and coefficient
comparisons. They do not certify equivalence between mathematical formulas and
code, or the analytic proof. The supported reproduction commands above use
temporary copies and leave the supplied verification inputs unchanged.
