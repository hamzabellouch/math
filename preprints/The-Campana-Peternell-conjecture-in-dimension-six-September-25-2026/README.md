# [The Campana–Peternell conjecture in dimension six](main.pdf)

**Author:** OpenAI

**Date:** September 25, 2026

## Citation

```bibtex
@misc{OAI:The-Campana-Peternell-conjecture-in-dimension-six-September-25-2026,
  author = {{OpenAI}},
  title = {{The Campana--Peternell conjecture in dimension six}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/The-Campana-Peternell-conjecture-in-dimension-six-September-25-2026/main.pdf}{OAI:The-Campana-Peternell-conjecture-in-dimension-six-September-25-2026}},
  year = {2026}
}
```

## Verification

Use Python 3.12.13 with SymPy 1.14.0 and NumPy 2.3.5. From this paper directory, run the exact-arithmetic certificate with assertions enabled:

```sh
env -u PYTHONOPTIMIZE python3 -u verification/verify.py
```

Successful execution prints `N done` followed by `pass`. The program checks the finite calculations documented in the paper's appendix.
