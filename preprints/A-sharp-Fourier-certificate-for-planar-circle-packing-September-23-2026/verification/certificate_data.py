"""Validate the public certificate manifest and all exact displayed tables."""

from pathlib import Path
import hashlib
import json
import platform

VERIFICATION_DIR = Path(__file__).resolve().parent
WRITEUP_DIR = VERIFICATION_DIR.parent
EXPECTED_SHA = "f967c6559e568142f1a9c174f54e7087bfa7934dc7f38792084db6351c5676c4"


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _integer_rows(text):
    return [[int(value) for value in line.split()]
            for line in text.strip().splitlines() if line.strip()]


def _tex_integer_rows(text):
    rows = []
    for line in text.strip().splitlines():
        line = line.strip()
        if not line:
            continue
        assert line.endswith("\\\\"), "TeX data row lacks row terminator"
        rows.append([int(value.strip()) for value in line[:-2].split("&")])
    return rows


def load_data():
    """Return tables after exact comparison with the public manifest.

    The fixed digest identifies this mathematical certificate's complete
    input specification. Independently parsed TSV and TeX tables must agree
    as integer arrays. No internal submission or historical review is needed.
    """
    if not __debug__:
        raise RuntimeError("Run without -O: certificate assertions are required")
    source_path = VERIFICATION_DIR / "data" / "certificate-inputs.json"
    source_sha256 = sha256(source_path)
    assert source_sha256 == EXPECTED_SHA, "Certificate manifest hash mismatch"
    manifest = json.loads(source_path.read_text())
    assert manifest["schema"] == "planar-fourier-packing-certificate-inputs-v1"
    tables = manifest["tables"]
    paths = {}
    parsed = {}
    for name in ("coefficients", "W_plus", "W_minus"):
        table = tables[name]
        expected_scale = 10**10 if name == "coefficients" else 10**4
        assert table["scale_denominator"] == expected_scale
        tsv_path = VERIFICATION_DIR / "data" / (name + ".tsv")
        tex_path = WRITEUP_DIR / "build" / "data" / (name + ".tex")
        rows = _integer_rows(tsv_path.read_text())
        assert rows == table["rows"], "TSV differs from public manifest: " + name
        assert _tex_integer_rows(tex_path.read_text()) == rows, "TeX differs from TSV: " + name
        for path in (tsv_path, tex_path):
            assert sha256(path) == manifest["files_sha256"][path.name], "Data hash mismatch: " + path.name
            paths[path.name] = path
        parsed[name] = rows
    rows = parsed["coefficients"]
    assert len(rows) == 51 and all(len(row) == 5 for row in rows)
    for name in ("W_plus", "W_minus"):
        assert len(parsed[name]) == 6 and all(len(row) == 6 for row in parsed[name])
    nodes = [row[0] for row in rows]
    assert nodes == [n for n in range(1, 101) if n % 12 in {0, 1, 3, 4, 7, 9}]
    return {
        "source_path": source_path,
        "source_sha256": source_sha256,
        "data_sha256": {name: sha256(path) for name, path in paths.items()},
        "rows": rows,
        "nodes": nodes,
        "W_plus": parsed["W_plus"],
        "W_minus": parsed["W_minus"],
        "data_identities_match": True,
    }


def provenance(data, script_path):
    return {
        "source_sha256": data["source_sha256"],
        "source_kind": "public certificate input manifest",
        "data_sha256": data["data_sha256"],
        "data_identities_match": data["data_identities_match"],
        "python_version": platform.python_version(),
        "certificate_file": Path(script_path).name,
        "certificate_sha256": sha256(script_path),
    }


def write_result(name, result):
    output_dir = VERIFICATION_DIR / "results"
    output_dir.mkdir(exist_ok=True)
    path = output_dir / name
    path.write_text(json.dumps(result, indent=2) + "\n")
    return path
