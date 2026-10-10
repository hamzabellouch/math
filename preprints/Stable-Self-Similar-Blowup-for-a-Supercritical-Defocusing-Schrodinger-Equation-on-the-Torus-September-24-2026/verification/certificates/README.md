# Exact finite-arithmetic verification

Requires Python 3.8 or later with only the standard library, and GNU `sha256sum`. From the `verification/` directory, run:

```sh
python3 -B certificates/exact_verifier.py > current-results.json
python3 - <<'PY'
import hashlib
import json
from pathlib import Path

def unique_object(pairs):
    result = dict(pairs)
    if len(result) != len(pairs):
        raise ValueError("Duplicate JSON key")
    return result

current = json.loads(Path("current-results.json").read_text(), object_pairs_hook=unique_object)
historical = json.loads(Path("certificates/RESULTS.json").read_text(), object_pairs_hook=unique_object)
for key, source in (
    ("adapted_verifier_sha256", "certificates/exact_verifier.py"),
    ("original_verifier_sha256", "certificates/original_exact_certificates.py"),
):
    if current.get(key) != hashlib.sha256(Path(source).read_bytes()).hexdigest():
        raise SystemExit(f"Current {key} does not match its source file")
    del current[key]
    del historical[key]
for key in ("input_sha256", "input_bytes", "input_lines"):
    if key in current:
        raise SystemExit(f"Removed input field is still present: {key}")
    del historical[key]
canonical = lambda value: json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)
if canonical(current) != canonical(historical):
    raise SystemExit("A preserved result field or value differs")
print("All preserved result fields match: PASS")
PY
(cd certificates && sha256sum -c CURRENT-SHA256SUMS)
```

The first command writes the current JSON result. The comparison permits only the three removed transcript-input fields and the two source-hash changes; it validates both current source hashes against the actual files and requires every other field and value to match `RESULTS.json`. Success requires exit status 0 from every command, the comparison's `PASS` message, and `OK` for all four file identities.

The JSON lists the mathematical inputs assumed by these finite computations. In particular, the manuscript supplies the K=8 reality, evenness, and degree-at-most-30 identity and the K=5 degree bounds `deg(d) <= 10`, `deg(c) <= 9`, and `deg(Im(c)) <= 8`; central cancellation is only a consistency check. The verifier does not establish the analytic arguments connecting its finite comparisons to the theorem.

`RESULTS.json` and `SHA256SUMS` remain historical records. `CURRENT-SHA256SUMS` records the current identities of the same four surviving files; it is not an execution receipt.
