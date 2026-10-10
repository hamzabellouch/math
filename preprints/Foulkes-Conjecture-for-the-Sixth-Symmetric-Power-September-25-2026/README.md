# [Foulkes' conjecture for the sixth symmetric power](main.pdf)

**Author:** OpenAI

**Date:** September 25, 2026

## Citation

```bibtex
@misc{OAI:Foulkes-Conjecture-for-the-Sixth-Symmetric-Power-September-25-2026,
  author = {{OpenAI}},
  title = {{Foulkes' conjecture for the sixth symmetric power}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Foulkes-Conjecture-for-the-Sixth-Symmetric-Power-September-25-2026/main.pdf}{OAI:Foulkes-Conjecture-for-the-Sixth-Symmetric-Power-September-25-2026}},
  year = {2026}
}
```

## Verification

Requires Python 3.9 or later. Run the supplied read-only checks from this paper
directory:

```sh
python3 -B verification/verify_computations.py --check
```

Success prints `PASS` and confirms the bundled source and reference-stream
identities, all 62 expected numeric rows, agreement with the manuscript tables,
and the stated numerical bounds. This command does not execute the C++ programs.

To compile and run both complete exact computations, GNU C++ with signed
128-bit integers and Boost headers is also required:

```sh
python3 -B verification/verify_computations.py --run --serial
```

Alternatively, replace `--serial` with `--threads 2` to use OpenMP for Appendix A.
Assertions remain enabled. A successful full run prints `PASS` after both
programs exit successfully and their complete output streams match the reference
bytes. It records compiler and execution details in a new temporary directory
outside the paper; `--output PATH` selects a new external directory instead.
