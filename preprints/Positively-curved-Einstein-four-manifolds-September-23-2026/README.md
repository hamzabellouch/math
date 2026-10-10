# [Positively curved Einstein four-manifolds](paper.pdf)

OpenAI · September 23, 2026

## Citation

```bibtex
@misc{OAI:Positively-curved-Einstein-four-manifolds-September-23-2026,
  author = {{OpenAI}},
  title = {{Positively curved Einstein four-manifolds}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf}{OAI:Positively-curved-Einstein-four-manifolds-September-23-2026}},
  year = {2026}
}
```

## Verification

The exact-arithmetic checker requires Python 3.10 or later and only the standard library. Run from this paper directory:

```sh
python3 -B verification/verify.py --check
```

Success means exit status zero and `all_passed: true`, with 53 identities, 15 reported univariate certificate rows plus 6 supplementary rows, 12 triangle certificate rows, and 24 additional exact-value assertions. The command recomputes the complete deterministic result and compares it with `verification/results.json`.

These are finite arithmetic checks, not a proof-assistant formalization of the whole argument. The precise scope and its distinction from the mathematical reductions proved in the paper are recorded in [verification/COVERAGE.md](verification/COVERAGE.md). Additional package-level reproduction instructions are in [verification/README.md](verification/README.md).
