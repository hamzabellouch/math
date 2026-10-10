# The 35-move certificate

Requires Python 3.10 or later with only the standard library. From this directory, run:

```sh
python3 -B -I verify_certificate.py
python3 -B -I independent_certificate.py
python3 -B -I independent_opening.py
```

Each checker reads the adjacent `certificate.txt` by default and accepts `--certificate PATH` (also `--table PATH`), `--json PATH`, and `--templates-json PATH`. The independent certificate checker also accepts `--rows-json PATH`. JSON output parents must exist.

Success is exit status 0 and `status: PASS` in the JSON summary printed on standard output.
