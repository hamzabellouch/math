# [Zero-Plane Rigidity for Einstein Four-Manifolds](einstein-boundary.pdf)

**Author:** OpenAI

**Date:** October 4, 2026

## Citation

```bibtex
@misc{OAI:Zero-Plane-Rigidity-for-Einstein-Four-Manifolds-October-4-2026,
  author = {{OpenAI}},
  title = {{Zero-Plane Rigidity for Einstein Four-Manifolds}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Zero-Plane-Rigidity-for-Einstein-Four-Manifolds-October-4-2026/einstein-boundary.pdf}{OAI:Zero-Plane-Rigidity-for-Einstein-Four-Manifolds-October-4-2026}},
  year = {2026}
}
```

## Verification

The exact arithmetic checker requires Python 3.10 or later and only the
standard library. From this paper directory, run:

```sh
python3 -B verification/verify.py --check
```

Success means exit status zero and `all_passed: true`, with 53 identities,
21 univariate certificate rows (15 reported and 6 supplementary), 12 triangle
certificate rows, and 24 exact-value assertions. The checker compares its
results with `verification/results.json`; its scope is documented in
`verification/COVERAGE.md`. It checks finite arithmetic, not the geometric
and analytic arguments.
