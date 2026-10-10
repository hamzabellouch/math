# Square numerical certificate

## Prerequisites

- Python 3.9 or later, with assertions enabled.
- A POSIX system with `fork`.
- A C++17 compiler with signed 128-bit integers, 64-bit `long`, arithmetic signed right shift, and UndefinedBehaviorSanitizer. Do not define `NDEBUG`.
- GMP C++ headers and libraries for chart regeneration.

`reproduce.py --help` lists compiler and GMP options. The driver installs nothing and makes no network requests.

## Run

From this directory, create an empty output directory and regenerate both charts:

```sh
certificate_output="$(mktemp -d)"
python3 -B reproduce.py --cxx 'g++ -fsanitize=undefined -fno-sanitize-recover=all' --work-dir "$certificate_output"
python3 -B verify_manuscript_bounds.py --work-dir "$certificate_output"
```

To reuse the supplied hash-verified charts instead:

```sh
certificate_output="$(mktemp -d)"
python3 -B reproduce.py --reuse-charts --cxx 'g++ -fsanitize=undefined -fno-sanitize-recover=all' --work-dir "$certificate_output"
python3 -B verify_manuscript_bounds.py --work-dir "$certificate_output"
```

`--reuse-charts` checks chart hashes but does not regenerate their coefficient recurrences. Use a new or empty output directory outside `verification/`; the postcheck refuses to overwrite its report.

## Inputs and outputs

| Path | Contents |
| --- | --- |
| `checkers/` | Numerical generators and checkers |
| `inputs/` | Barrier coefficients and two exact charts |
| `certificates/` | Reference bounds and sector-input hashes |
| `package-manifest.json` | File sizes and SHA-256 hashes |

`reproduce.py` writes logs, `driver-provenance.json`, and `local-check/verification-summary.json` under the output directory. It succeeds only with exit status zero and `All numerical stages passed.`

`verify_manuscript_bounds.py` writes `manuscript-bounds.json` there by default. Success is exit status zero and a line beginning `PASS: exact manuscript bounds`.

These commands check finite arithmetic and numerical interfaces. The tensor constructions and analytic error bounds are supplied by the manuscript.
