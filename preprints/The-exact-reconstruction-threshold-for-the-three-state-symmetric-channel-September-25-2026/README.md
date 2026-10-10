# [The exact reconstruction threshold for the three-state symmetric channel](paper.pdf)

**Author:** OpenAI

**Date:** September 25, 2026

## Citation

To cite this manuscript:

```bibtex
@misc{OAI:The-exact-reconstruction-threshold-for-the-three-state-symmetric-channel-September-25-2026,
  author = {{OpenAI}},
  title = {{The exact reconstruction threshold for the three-state symmetric channel}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/The-exact-reconstruction-threshold-for-the-three-state-symmetric-channel-September-25-2026/paper.pdf}{OAI:The-exact-reconstruction-threshold-for-the-three-state-symmetric-channel-September-25-2026}},
  year = {2026}
}
```

## Verification

Use Python 3.9 or newer with SymPy, and a `g++` supporting C++17, signed `__int128`, and a plain `int` type of at least 32 bits. Run from this paper directory, choosing a new output directory outside `verification/`:

```sh
python3 -B verification/reproduce.py --output-dir .verification-output --jobs 2
```

The complete replay succeeds when `.verification-output/summary.json` has `passed: true` and 37 passing subprocess records. Do not use Python's `-O` or `-OO` options or define `NDEBUG`.

Run the supplemental interval undefined-behavior check as well:

```sh
g++ -std=c++17 -O2 -UNDEBUG -fsanitize=undefined -fno-sanitize-recover=undefined verification/interval.cpp -o .verification-output/interval-ubsan
for j in 0 1 2; do .verification-output/interval-ubsan "$j"; done
```

All three cases must exit zero without sanitizer diagnostics and end at visited-box totals 414080, 756096, and 1004426, respectively. `verification/README.md` is the verification guide.
