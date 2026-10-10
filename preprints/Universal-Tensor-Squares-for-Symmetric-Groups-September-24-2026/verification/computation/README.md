# Finite verification

Requires Linux, Bash, Python 3.9 or later, and GNU C++ with C++17 and `unsigned __int128` support. Python assertions must be enabled.

The programs are in `../code/`; the logs in this directory are stored results. Run from the article directory in a temporary copy:

```sh
set -euo pipefail
verification_work=$(mktemp -d)
cp -R verification "$verification_work/"
cd "$verification_work/verification/code"
g++ -O3 -std=c++17 smallcode_submitted.cpp -o smallcode_submitted
env -u PYTHONOPTIMIZE python3 -B smallcode_verify.py runs 1 3 {5..8} {10..64} \
  --seconds 300 --log ../computation/recheck-61-degrees.log
env -u PYTHONOPTIMIZE python3 -B capacity_checks.py intermediate
env -u PYTHONOPTIMIZE python3 -B capacity_checks.py exceptional
```

Success requires status 0 for every listed degree and `PASS` from both capacity checks. Do not add the excluded degrees 2, 4, or 9. Each character child is limited to 1536 MiB of address space and 300 seconds of wall time; a timeout or failed run is not a certificate.

Generated files remain in the temporary copy. These commands check finite character and capacity cases, not the article's general recurrence, pruning, or analytic arguments.

The README hash in historical `RESULTS.json` identifies the pre-sanitization documentation, not this current guide; no verifier consumes that binding.
