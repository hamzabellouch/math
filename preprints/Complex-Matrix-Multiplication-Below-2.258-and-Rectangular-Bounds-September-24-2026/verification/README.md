# Verification

This directory contains two verification packages:

| Path | Purpose |
| --- | --- |
| [`certificate/`](certificate/README.md) | Exact numerical checks for the square bound |
| [`certificates/`](certificates/CERTIFICATES.md) | Rectangular rational and finite-support checks |
| `scripts/check_certificate.py` | Byte-count and SHA-256 inventory checks |

The package READMEs give their prerequisites, run commands, outputs, and success criteria. Keep generated output outside this directory.

## Inventory check

Requires Python 3.9 or later; only the standard library is used.

From the paper directory, run:

```sh
python3 -B verification/scripts/check_certificate.py
```

The command reads `BUILD-INPUTS.json` and `certificate/package-manifest.json`. A zero exit status and a line beginning `PASS:` mean the listed file sets, byte counts, and hashes match. This command does not run the numerical checks.
