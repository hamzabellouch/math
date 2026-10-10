# [A sharp entropy bound and the simplex inequality for isotropic constants](isotropic-simplex.pdf)

**Author:** OpenAI

**Date:** October 5, 2026

## Citation

```bibtex
@misc{OAI:A-sharp-entropy-bound-and-the-simplex-inequality-for-isotropic-constants-October-5-2026,
  author = {{OpenAI}},
  title = {{A sharp entropy bound and the simplex inequality for isotropic constants}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/A-sharp-entropy-bound-and-the-simplex-inequality-for-isotropic-constants-October-5-2026/isotropic-simplex.pdf}{OAI:A-sharp-entropy-bound-and-the-simplex-inequality-for-isotropic-constants-October-5-2026}},
  year = {2026}
}
```

## Verification

The scalar certificate checker uses only Python 3's standard library and
exact rational arithmetic. From this paper's root directory, run:

```sh
python3 verification/verify_scalar.py
```

A successful run exits with status zero and ends with `ALL CHECKS PASSED`.
It checks the rational bounds used in the scalar estimates; the analytic
inputs are proved in the paper's appendix.
