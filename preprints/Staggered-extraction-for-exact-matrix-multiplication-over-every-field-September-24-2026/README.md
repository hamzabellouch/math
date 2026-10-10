# [Staggered extraction for exact matrix multiplication over every field](Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf)

**Author:** OpenAI

**Date:** September 24, 2026

## Citation

```bibtex
@misc{OAI:Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026,
  author = {{OpenAI}},
  title = {{Staggered extraction for exact matrix multiplication over every field}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf}{OAI:Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026}},
  year = {2026}
}
```

## Verification

Use Python 3.10 or later with `mpmath==1.3.0`, as specified in `verification/data/requirements.txt`. Keep assertions enabled. From this paper directory, run both interval modes with fresh output paths:

```sh
matrix_verification_output="$(python3 -c 'import pathlib, tempfile; print(pathlib.Path(tempfile.mkdtemp(prefix="matrix-all-fields-verify-")).resolve())')"
python3 -B verification/scripts/verify_parameters.py --mode interval --dps 80 --rational-log --output "$matrix_verification_output/rational-series.json"
python3 -B verification/scripts/verify_parameters.py --mode interval --dps 80 --output "$matrix_verification_output/native-log.json"
```

Every entry in each output's `checks` object should be true. The first mode uses a rational logarithm series with an explicit tail; the second is a directed native-logarithm cross-check. These calculations check the finite certificates, not the tensor constructions or limiting arguments.
