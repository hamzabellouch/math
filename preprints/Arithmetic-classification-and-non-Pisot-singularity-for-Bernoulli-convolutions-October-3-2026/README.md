# [Arithmetic classification and non-Pisot singularity for Bernoulli convolutions](paper.pdf)

**Author:** OpenAI

**Date:** October 3, 2026

## Citation

```bibtex
@misc{OAI:Arithmetic-classification-and-non-Pisot-singularity-for-Bernoulli-convolutions-October-3-2026,
  author = {{OpenAI}},
  title = {{Arithmetic classification and non-Pisot singularity for Bernoulli convolutions}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Arithmetic-classification-and-non-Pisot-singularity-for-Bernoulli-convolutions-October-3-2026/paper.pdf}{OAI:Arithmetic-classification-and-non-Pisot-singularity-for-Bernoulli-convolutions-October-3-2026}},
  year = {2026}
}
```

## Verification

The degree-31 certificate uses Python 3 and only its standard library. From this
paper directory, run without `-O` or `PYTHONOPTIMIZE`, since the verifier requires
assertions:

```sh
python3 verification/verify_degree31.py
```

Successful execution exits with status zero and prints
`PASS: all degree-31 finite arithmetic checks passed.` The script checks the
finite exact-arithmetic certificate; the analytic bounds connecting it to the
infinite products are supplied in the manuscript.
