# [The Mahler Conjecture for General Convex Bodies](paper.pdf)

**Author:** OpenAI

**Date:** September 22, 2026

## Citation

```bibtex
@misc{OAI:The-Mahler-Conjecture-for-General-Convex-Bodies-September-22-2026,
  author = {{OpenAI}},
  title = {{The Mahler Conjecture for General Convex Bodies}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/The-Mahler-Conjecture-for-General-Convex-Bodies-September-22-2026/paper.pdf}{OAI:The-Mahler-Conjecture-for-General-Convex-Bodies-September-22-2026}},
  year = {2026}
}
```

## Verification

Use Python 3 without `-O` or `PYTHONOPTIMIZE` and the dependency in `verification/requirements.txt` (`sympy==1.14.0`). The runner executes the ten scalar and segment computation programs from unchanged source in a new temporary output directory:

```sh
(
  set -eu
  verification_tmp=$(mktemp -d)
  printf 'Verification results: %s\n' "$verification_tmp/run"
  python3 verification/reproduce.py --output "$verification_tmp/run"
)
```

Successful execution prints ten `PASS` lines and writes `RUN.json` with `"passed": true`. The output also contains per-program logs and generated reports.
