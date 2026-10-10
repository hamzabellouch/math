# Independent interior certificate

From the article directory, run:

```sh
python3 -B verification/checks/reproduce.py
```

See [the check instructions](../checks/README.md) for prerequisites and the current table-check limitation. The runner uses `verification/checks/original/certificate-inputs.txt`; its first 1,124 lines contain the two exact table bodies, required labels and fences, and blank padding, keeping the embedded source outside the independent engine's input boundary.

`engine.py` and `bounds.py` implement the finite interior coefficient expansion and bounds. `compare_oracle.py` compares the independently generated results with the retained exact result. These checks do not establish the analytic reduction or the correspondence between the manuscript formulas and code.

The files in `output/` are historical records, not records of a new run on the sanitized input. `first-freeze.json` identifies the distributed publication copies of the frozen sources; only the engine's descriptive header was sanitized, with executable code unchanged. The historical oracle path is explicitly marked redacted. The runner authenticates the retained files, validates current input hashes separately, and compares the remaining result data without altering the historical outputs.
