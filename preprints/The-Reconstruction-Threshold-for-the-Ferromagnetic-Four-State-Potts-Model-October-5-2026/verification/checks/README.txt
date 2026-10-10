EXACT SIGN VERIFICATION

Run from the verification/ directory. Requirements: Python 3 with its standard
library, a C++17 compiler providing GCC-compatible bits/stdc++.h, and Boost
multiprecision headers. The C++ code requires at least 32-bit int and 64-bit
long long. Keep C++ and Python assertions enabled.

Complete checks:

  mkdir -p artifacts
  g++ -std=c++17 -O3 -UNDEBUG checks/certificate.cpp -o artifacts/certificate
  ./artifacts/certificate
  ./artifacts/certificate b
  python3 checks/small_polynomials.py

Success requires every command to exit with status 0. The two C++ runs write
progress to stderr and end with these lines, respectively:

  done 4479 19 lp=2074 lt=166
  done 1935 20 lp=871 lt=97

LIGHTWEIGHT CHECK

  python3 checks/verify.py

This requires g++ with UndefinedBehaviorSanitizer. It checks the scalar
polynomials and safety harness, validates the source extracted from
checks/certificate-source.txt, and validates checks/full-runs.json against the recorded
checks/logs/paper-mode-a.log and paper-mode-b.log. It does not repeat the full
C++ traversals. Success is exit status 0 with a receipt at
artifacts/checks/verification.json; generated binaries and logs are written
under artifacts/checks/.
