# [A finite-time singularity of Calabi flow on projective space](paper.pdf)

**Author:** OpenAI

**Date:** September 24, 2026

## Citation

```bibtex
@misc{OAI:A-finite-time-singularity-of-Calabi-flow-on-projective-space-September-24-2026,
  author = {{OpenAI}},
  title = {{A finite-time singularity of Calabi flow on projective space}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/A-finite-time-singularity-of-Calabi-flow-on-projective-space-September-24-2026/paper.pdf}{OAI:A-finite-time-singularity-of-Calabi-flow-on-projective-space-September-24-2026}},
  year = {2026}
}
```

## Verification

The exact certificate and supplementary rational checks require only Python 3's
standard library. Run with assertions enabled: do not use `-O` or `-OO`, and
unset `PYTHONOPTIMIZE` as below. These commands use a temporary copy because the
allowances check writes `arithmetic_allowances.json` beside its source file.

```sh
(
  set -eu
  work_dir="$(mktemp -d)"
  trap 'rm -rf "$work_dir"' 0 HUP INT TERM
  cp -R verification "$work_dir/verification"
  unset PYTHONOPTIMIZE
  python3 -B "$work_dir/verification/certificate.py"
  python3 -B "$work_dir/verification/arithmetic_allowances.py"
  # Optional supplementary root and tail check:
  python3 -B "$work_dir/verification/tail-check.py"
)
```

The certificate is silent on success. The allowances check prints a report with
`all_exact_rational_checks_pass` set to `true`, and the optional tail check prints
a message that all checks passed exactly. Successful execution means the
programs' assertions hold; it does not independently verify their analytic
interpretation or the full theorem.
