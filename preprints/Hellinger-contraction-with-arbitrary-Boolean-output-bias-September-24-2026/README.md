# [Hellinger contraction with arbitrary Boolean output bias](main.pdf)

**Author:** OpenAI

**Date:** September 24, 2026

## Citation

```bibtex
@misc{OAI:Hellinger-contraction-with-arbitrary-Boolean-output-bias-September-24-2026,
  author = {{OpenAI}},
  title = {{Hellinger contraction with arbitrary Boolean output bias}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Hellinger-contraction-with-arbitrary-Boolean-output-bias-September-24-2026/main.pdf}{OAI:Hellinger-contraction-with-arbitrary-Boolean-output-bias-September-24-2026}},
  year = {2026}
}
```

## Verification

The exact arithmetic checks require Python 3.9 or later with SymPy 1.14.0 and
a C++ compiler supporting signed `__int128`, such as GCC or Clang. Run with
assertions enabled; do not use Python's `-O` option or set `PYTHONOPTIMIZE`.
From this paper directory, run:

```sh
verification_output="$(mktemp -d)"
python3 verification/verify_all.py --output-dir "$verification_output"
```

The output directory must be new or empty. Success is exit code zero, a final
`PASS`, and `"status": "pass"` in `verification.json` under that output
directory. The runner records source hashes, commands, and separate logs. It
does not install dependencies or use network access. Use `--cxx clang++` to
select Clang when needed.
