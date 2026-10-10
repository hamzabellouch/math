# [The Reconstruction Threshold for the Ferromagnetic Four-State Potts Model](four-state-potts.pdf)

**Author:** OpenAI

**Date:** October 5, 2026

## Citation

```bibtex
@misc{OAI:The-Reconstruction-Threshold-for-the-Ferromagnetic-Four-State-Potts-Model-October-5-2026,
  author = {{OpenAI}},
  title = {{The Reconstruction Threshold for the Ferromagnetic Four-State Potts Model}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/The-Reconstruction-Threshold-for-the-Ferromagnetic-Four-State-Potts-Model-October-5-2026/four-state-potts.pdf}{OAI:The-Reconstruction-Threshold-for-the-Ferromagnetic-Four-State-Potts-Model-October-5-2026}},
  year = {2026}
}
```

## Verification

Use Python 3 without optimization, GCC-compatible C++17 with `bits/stdc++.h`
and Boost Multiprecision headers, and undefined-behavior sanitizer support.
From a temporary working copy of `verification/`, run:

```sh
python3 checks/verify.py
```

This reruns the rational polynomial checks and focused UBSan safety harness,
then checks the original source binding and retained full-traversal records.
Success writes `artifacts/checks/verification.json` with passing scalar,
symmetry, safety, and recorded-run checks; it does not repeat the long
certificate traversals. To repeat those full checks from the same directory:

```sh
mkdir -p artifacts
g++ -std=c++17 -O3 -UNDEBUG checks/certificate.cpp -o artifacts/certificate
./artifacts/certificate
./artifacts/certificate b
python3 checks/small_polynomials.py
```

The C++ modes must end with `done 4479 19 lp=2074 lt=166` and
`done 1935 20 lp=871 lt=97`, respectively. Assertions must remain enabled.
The exact certificate and scalar-check sources in `verification/checks/`
are also the paper's code-listing inputs.
