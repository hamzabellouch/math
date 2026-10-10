# The 25-move certificate

Requires Python 3.9 or later with only the standard library. From this directory, run:

```sh
python3 verify_certificate.py
python3 independent_certificate.py
```

Both checkers read the adjacent `certificate.txt` by default. They accept an optional certificate path and `--json` for a JSON result.

Success is exit status 0. Invalid certificate data produce `FAIL:` on standard error and a nonzero status.
