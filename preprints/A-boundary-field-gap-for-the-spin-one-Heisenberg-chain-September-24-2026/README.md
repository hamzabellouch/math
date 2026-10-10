# [A boundary-field gap for the spin-one Heisenberg chain](paper.pdf)

**Author:** OpenAI

**Date:** September 24, 2026

## Citation

```bibtex
@misc{OAI:A-boundary-field-gap-for-the-spin-one-Heisenberg-chain-September-24-2026,
  author = {{OpenAI}},
  title = {{A boundary-field gap for the spin-one Heisenberg chain}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/A-boundary-field-gap-for-the-spin-one-Heisenberg-chain-September-24-2026/paper.pdf}{OAI:A-boundary-field-gap-for-the-spin-one-Heisenberg-chain-September-24-2026}},
  year = {2026}
}
```

## Verification

The finite-computation programs require Python 3.11 or later with assertions
enabled. The scalar and trial programs use the standard library; the thermal
program also requires NumPy and SciPy. From this paper directory, use a fresh
replay directory so the shipped certificates are not overwritten:

```sh
article_dir="$PWD"
verification_output="$article_dir/.verification-output/computation-replay"
mkdir -p "$verification_output"
env -u PYTHONOPTIMIZE python3 -B "$article_dir/verification/scalar_checks.py" "$verification_output"
env -u PYTHONOPTIMIZE python3 -B "$article_dir/verification/trial_verify.py" "$verification_output"
(cd "$verification_output" && env -u PYTHONOPTIMIZE python3 -B "$article_dir/verification/thermal_certificate_check.py")
```

Successful commands exit with status zero. Use the exact stored-certificate
comparison in [verification/README.md](verification/README.md), which also
lists prerequisites, expected files, and the finite checks' scope and
limitations. These computations do not replace the analytic arguments.
