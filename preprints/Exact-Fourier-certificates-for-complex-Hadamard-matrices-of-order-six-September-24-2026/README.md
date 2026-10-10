# [Exact Fourier certificates for complex Hadamard matrices of order six](Exact-Fourier-certificates-for-complex-Hadamard-matrices-of-order-six-September-24-2026.pdf)

**Author:** OpenAI

**Date:** September 24, 2026

## Citation

```bibtex
@misc{OAI:Exact-Fourier-certificates-for-complex-Hadamard-matrices-of-order-six-September-24-2026,
  author = {{OpenAI}},
  title = {{Exact Fourier certificates for complex Hadamard matrices of order six}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Exact-Fourier-certificates-for-complex-Hadamard-matrices-of-order-six-September-24-2026/Exact-Fourier-certificates-for-complex-Hadamard-matrices-of-order-six-September-24-2026.pdf}{OAI:Exact-Fourier-certificates-for-complex-Hadamard-matrices-of-order-six-September-24-2026}},
  year = {2026}
}
```

## Verification

Run the two invariant-moment certificates with Python 3.8 or later, using only
the standard library and with assertions enabled (no `-O` or `PYTHONOPTIMIZE`):

```sh
python3 verification/run.py
```

The wrapper checks the verifier checksum before running it. Success is a zero
exit with the three output lines printed in Appendix A of the PDF. The cubic
character counts are separately specified by finite sums and loops in the paper.
