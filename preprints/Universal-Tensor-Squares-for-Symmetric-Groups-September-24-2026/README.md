# [Universal Tensor Squares for Symmetric Groups](main.pdf)

**Author:** OpenAI

**Date:** September 24, 2026

## Citation

```bibtex
@misc{OAI:Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026,
  author = {{OpenAI}},
  title = {{Universal Tensor Squares for Symmetric Groups}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf}{OAI:Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026}},
  year = {2026}
}
```

## Verification

Use Linux, Bash, Python 3.9 or later, and GNU C++ with C++17 and
`unsigned __int128` support. The supplementary comparison also requires the
undefined-behavior sanitizer runtime. Python assertions must be enabled.

Run the complete finite checks from this paper directory in a temporary copy:

```sh
set -euo pipefail
verification_work=$(mktemp -d)
cp -R verification "$verification_work/"
cd "$verification_work/verification/code"
g++ -O3 -std=c++17 smallcode_submitted.cpp -o smallcode_submitted
env -u PYTHONOPTIMIZE python3 -B smallcode_verify.py runs 1 3 {5..8} {10..64} \
  --seconds 300 --log ../computation/recheck-61-degrees.log
env -u PYTHONOPTIMIZE python3 -B capacity_checks.py intermediate
env -u PYTHONOPTIMIZE python3 -B capacity_checks.py exceptional
```

Each child of the character driver has a 1536-MiB address-space limit and a
300-second wall limit. Success requires status 0 for every listed degree and
`PASS` from both capacity checks; a timeout or failed run is not a successful
verification. The excluded degrees 2, 4, and 9 must not be included in this run.

From the same temporary `code` directory, run the supplementary checks:

```sh
env -u PYTHONOPTIMIZE python3 -B capacity_independent.py
g++ -O2 -std=c++17 -fsanitize=undefined \
  -fno-sanitize-recover=all smallcode_dump.cpp -o smallcode_dump_ubsan
env -u PYTHONOPTIMIZE python3 -B smallcode_verify.py compare {1..12} \
  --log ../computation/recheck-independent.log
env -u PYTHONOPTIMIZE python3 -B -m unittest -v test_smallcode_verify.py
```

Success requires status 0 for each command, `PASS` for each independent
comparison, and no unittest failures. Generated binaries and rerun logs remain
in the temporary copy. The build uses the source listings under `verification/code/`;
the executable verification sources are under `verification/code/`.
