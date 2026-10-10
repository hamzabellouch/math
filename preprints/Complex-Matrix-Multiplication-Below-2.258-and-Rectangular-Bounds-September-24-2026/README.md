# [Complex Matrix Multiplication Below 2.258 and Rectangular Bounds](Complex-Matrix-Multiplication-Below-2.258-and-Rectangular-Bounds-September-24-2026.pdf)

**Author:** OpenAI

**Date:** September 24, 2026

## Citation

```bibtex
@misc{OAI:Complex-Matrix-Multiplication-Below-2.258-and-Rectangular-Bounds-September-24-2026,
  author = {{OpenAI}},
  title = {{Complex Matrix Multiplication Below $2.258$ and Rectangular Bounds}},
  howpublished = {OpenAI Math Release preprint
                  \href{https://github.com/openai/math/blob/main/preprints/Complex-Matrix-Multiplication-Below-2.258-and-Rectangular-Bounds-September-24-2026/Complex-Matrix-Multiplication-Below-2.258-and-Rectangular-Bounds-September-24-2026.pdf}{OAI:Complex-Matrix-Multiplication-Below-2.258-and-Rectangular-Bounds-September-24-2026}},
  year = {2026}
}
```

## Verification

First check the numerical payload and build-input inventory:

```sh
python3 -B verification/scripts/check_certificate.py
```

A zero exit status confirms input integrity only; it does not execute the numerical proof.

The full square-certificate replay requires Python 3.9 or later, POSIX `fork`, a C++17 compiler with signed 128-bit integers, a 64-bit `long`, arithmetic signed right shift, UndefinedBehaviorSanitizer, and GMP C++ headers and libraries. Keep Python and C++ assertions enabled. From this paper directory, run:

```sh
certificate_output="$(python3 -c 'import pathlib, tempfile, uuid; print(pathlib.Path(tempfile.gettempdir()).resolve() / ("matrix-square-certificate-" + uuid.uuid4().hex))')"
python3 -B verification/certificate/reproduce.py --cxx 'g++ -fsanitize=undefined -fno-sanitize-recover=all' --work-dir "$certificate_output"
python3 -B verification/certificate/verify_manuscript_bounds.py --work-dir "$certificate_output"
```

Both commands must exit successfully. They check finite arithmetic interfaces; the tensor constructions and analytic allowances remain statements proved in the manuscript.

Run the default rectangular checks in a fresh writable copy because they write results beside their inputs:

```sh
rectangular_work="$(mktemp -d)"
cp -R verification/certificates "$rectangular_work/certificates"
python3 -B "$rectangular_work/certificates/checks/run_checks.py"
```

The default checks use only the Python standard library and succeed with a zero exit status. Optional `--numerics` diagnostics require `mpmath==1.3.0` and are high-precision evaluations, not rigorous interval certificates.
