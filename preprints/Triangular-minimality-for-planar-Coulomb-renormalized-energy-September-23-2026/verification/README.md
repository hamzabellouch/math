# Exact interval certificate

## Files and requirements

- `certificate.cpp`, `core.hpp`, and `grids.hpp` implement the finite scalar
  calculation.
- `run-certificate.py` compiles and runs it.
- `data/certificate-record.txt` retains the source/formula bindings, completed-run
  metadata, saved integer pairs, and interpretations referenced by the manuscript.
  It is evidence for readers, not an input to the runner.

Requires Python 3, `g++` with C++17 and OpenMP support, and the
Boost.Multiprecision headers. The target must have an `int` type at least 32 bits
wide. The wrapper uses `-O3 -fopenmp` and `OMP_NUM_THREADS=32`; compilation with
`NDEBUG` is rejected so assertions remain enabled.

## Run

From this directory:

```sh
python3 run-certificate.py --output-dir certificate-run
```

Relative output paths are resolved from the current working directory. The
default, if `--output-dir` is omitted, is `certificate-run` beside the script.
Use a new directory for each run; existing generated files are replaced.

## Outputs and success

The output directory receives the compiled `certificate`, `compile.log`,
`run.log`, and `run-receipt.json`.

Success requires exit status 0, terminal `OK`, and
`"sources_unchanged": true`, `"terminal_OK": true`, and
`"stage_validation": {"passed": true, ...}` in the receipt. The wrapper checks
the expected stage order and mesh markers; inspect the log and receipt together.

The wrapper does not read the manuscript. The finite checks rely on the
manuscript's analytic bounds and its explanation of the energy conclusion.
