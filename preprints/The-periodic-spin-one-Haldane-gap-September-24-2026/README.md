# [The periodic spin-one Haldane gap](paper.pdf)

**Author:** OpenAI

**Date:** September 24, 2026

## Citation

```bibtex
@misc{OAI:The-periodic-spin-one-Haldane-gap-September-24-2026,
  author = {{OpenAI}},
  title = {{The periodic spin-one Haldane gap}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/The-periodic-spin-one-Haldane-gap-September-24-2026/paper.pdf}{OAI:The-periodic-spin-one-Haldane-gap-September-24-2026}},
  year = {2026}
}
```

## Verification

The finite verifier requires Python 3, NumPy, and SciPy with assertions enabled.
For a complete fresh recomputation, run from this paper directory with a new
explicit output directory:

```sh
env -u PYTHONOPTIMIZE python3 -B verification/verify.py \
  --output "$PWD/.verification-output/full-001"
```

Choose a new output directory for each run. A successful full run writes
`verification.json` with `success: true` and `full_recomputation: true`.
The existing `--only` selections and `--workers` option are unchanged; see
[verification/computations/README.md](verification/computations/README.md) for
tested versions, commands, runtimes, and exact scope. Partial selections
explicitly label remaining certificate records as frozen evidence. These
finite checks do not replace the analytic uniform-gap argument.
