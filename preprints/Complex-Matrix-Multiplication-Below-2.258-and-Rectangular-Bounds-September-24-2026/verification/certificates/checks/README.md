# Run the rectangular checks

The checks require Python 3.7 or later and only its standard library. Assertions must be enabled: do not use `-O` or set `PYTHONOPTIMIZE`. The commands below use a POSIX shell with `mktemp` and `cp`.

From the parent `verification/certificates/` directory, run in a fresh writable copy:

```sh
rectangular_work="$(mktemp -d)"
cp -R checks "$rectangular_work/checks"
python3 -B "$rectangular_work/checks/run_checks.py"
```

All input paths are resolved relative to the scripts. Each checker writes its matching `.json` file; the runner writes `execution_report.json`. A zero exit status and printed JSON with `"status": "passed"` indicate success, including canonical-output and script/data-hash checks.
