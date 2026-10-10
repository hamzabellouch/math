# The 21-move certificate

Requires Python 3.10 or later with only the standard library. From this directory, run:

```sh
python3 primary.py
python3 independent.py
```

Both checkers read the adjacent `certificate.txt` by default and print a JSON summary. Use `--table PATH` to select another input and `--output PATH` to write the reconstructed cards and combinations; the output parent must exist.

Success is exit status 0 and `status: PASS` in the JSON summary.
