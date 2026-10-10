# [A counterexample to integer-degree harmonic dimension comparison](paper.pdf)

**Author:** OpenAI

**Date:** September 25, 2026

## Citation

```bibtex
@misc{OAI:A-counterexample-to-integer-degree-harmonic-dimension-comparison-September-25-2026,
  author = {{OpenAI}},
  title = {{A counterexample to integer-degree harmonic dimension comparison}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/A-counterexample-to-integer-degree-harmonic-dimension-comparison-September-25-2026/paper.pdf}{OAI:A-counterexample-to-integer-degree-harmonic-dimension-comparison-September-25-2026}},
  year = {2026}
}
```

## Verification

Use Python 3.8 or later; the finite spectral-selection check uses only the standard library. From this paper directory, run with assertions enabled:

```sh
env -u PYTHONOPTIMIZE python3 verification/counting-check.py
```

Successful execution exits zero and prints `exact count proves (3): True`. This checks the finite selection at dimension 16 and degree 50000; the verification package retains its detailed scope and recorded output.
