# [Entanglement with zero distillable secret key in local dimension ten](paper.pdf)

**Author:** OpenAI

**Date:** September 27, 2026

## Citation

To cite this manuscript:

```bibtex
@misc{OAI:Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026,
  author = {{OpenAI}},
  title = {{Entanglement with zero distillable secret key in local dimension ten}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf}{OAI:Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026}},
  year = {2026}
}
```

## Verification

The optional supplementary checks use Python 3 and only its standard library, with exact integer arithmetic. Run with assertions enabled, without `-O` or `-OO`. The commands below use a temporary copy and compare the replayed outputs with the included recorded outputs:

```sh
set -eu
unset PYTHONOPTIMIZE
verification_run=$(mktemp -d "${TMPDIR:-/tmp}/zero-key-verification.XXXXXX")
cp -R verification "$verification_run/verification"
python3 "$verification_run/verification/combinatorics_exact_checks.py" > "$verification_run/combinatorics.stdout"
cmp "$verification_run/verification/combinatorics_exact_checks.json" verification/combinatorics_exact_checks.json
python3 "$verification_run/verification/gadget_exact_check.py" > "$verification_run/gadget.json"
cmp "$verification_run/gadget.json" verification/gadget_exact_check.json
python3 "$verification_run/verification/exact_certificate.py" > "$verification_run/certificate-output.txt"
cmp "$verification_run/certificate-output.txt" verification/certificate-output.txt
```

Success means all programs and comparisons exit zero. These finite checks cover only the arithmetic components described in the paper; they do not establish the full paper or instantiate the enormous global matrices. The PDF build does not run them.
