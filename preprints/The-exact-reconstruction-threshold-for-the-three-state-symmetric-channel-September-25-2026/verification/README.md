# Exact mathematical certificates

Requires Python 3.9 or newer, SymPy, and `g++` with C++17, signed `__int128`,
a plain `int` type of at least 32 bits, and undefined-behavior sanitizer support.
Do not use Python's `-O` or `-OO` options or define `NDEBUG`.

## Complete replay

From the paper directory, run:

```sh
python3 -B verification/reproduce.py --output-dir checks/my-replay --jobs 2
```

The output directory must be new and outside `verification/`. The runner checks
source identities, compiles the C++ programs, and runs all certificate cases.
Success requires exit status zero and `summary.json` with `passed: true` and
37 passing subprocess records. Logs and individual records are written to the
chosen output directory. `--jobs` controls local concurrency and defaults to one.

## Required interval sanitizer check

Run this separately from the paper directory:

```sh
g++ -std=c++17 -O2 -UNDEBUG -fsanitize=undefined \
    -fno-sanitize-recover=undefined verification/interval.cpp -o interval-ubsan
for j in 0 1 2; do ./interval-ubsan "$j"; done
```

All three runs must exit zero without sanitizer diagnostics and end at visited-box
totals 414080, 756096, and 1004426 for cases 0, 1, and 2, respectively.
