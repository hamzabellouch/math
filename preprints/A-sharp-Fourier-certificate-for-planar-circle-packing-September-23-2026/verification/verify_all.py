#!/usr/bin/env python3
"""Run the finite and scalar Arb certificates, then write their results."""

import json

from certificate_data import VERIFICATION_DIR, sha256, write_result
from interval_certificate import run_certificate as run_finite
from interval_bounds import run_certificate as run_scalar


def main():
    finite = run_finite()
    scalar = run_scalar(finite)
    assert finite.result["status"] == scalar["status"] == "pass"
    assert finite.result["source_sha256"] == scalar["source_sha256"]
    assert finite.result["data_sha256"] == scalar["data_sha256"]
    result = {
        "status": "pass",
        "source_sha256": finite.result["source_sha256"],
        "data_sha256": finite.result["data_sha256"],
        "data_identities_match": finite.result["data_identities_match"],
        "python_version": finite.result["python_version"],
        "python_flint_version": finite.result["python_flint_version"],
        "precision_bits": finite.result["precision_bits"],
        "coverage": finite.result["coverage"],
        "certificate_sources_sha256": {
            path.name: sha256(path)
            for path in sorted(VERIFICATION_DIR.glob("*.py"))
        },
        "result_files": ["finite.json", "scalar.json"],
    }
    write_result("summary.json", result)
    print(json.dumps(result, indent=2), flush=True)
    return result


if __name__ == "__main__":
    main()
