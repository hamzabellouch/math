#!/usr/bin/env python3
"""Verify the clean numerical and article-build input inventories."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def require(condition, message):
    if not condition:
        raise ValueError(message)


def safe_path(base, name):
    item = PurePosixPath(name)
    require(not item.is_absolute() and bool(item.parts) and
            all(part not in ("", ".", "..") for part in item.parts),
            "Unsafe inventory path: " + name)
    path = base.joinpath(*item.parts)
    require(not path.is_symlink() and path.is_file(), "Missing or symlinked file: " + name)
    require(path.resolve().is_relative_to(base.resolve()), "Path escapes inventory root")
    return path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    root = args.root.resolve()
    certificate = root / "certificate"
    manifest_path = certificate / "package-manifest.json"
    manifest = json.loads(manifest_path.read_text())
    rows = manifest["files"]
    names = [row["path"] for row in rows]
    require(len(set(names)) == len(names), "Duplicate curated inventory entries")
    actual = {str(path.relative_to(certificate)) for path in certificate.rglob("*") if path.is_file()}
    require(actual == set(names) | {"package-manifest.json"},
            "Curated certificate file set differs from its manifest")
    for row in rows:
        path = safe_path(certificate, row["path"])
        require(path.stat().st_size == row["bytes"] and sha(path) == row["sha256"],
                "Curated file hash/size mismatch: " + row["path"])
    package = root.parent
    inputs = json.loads((root / "BUILD-INPUTS.json").read_text())["files"]
    input_names = [row["path"] for row in inputs]
    require(len(set(input_names)) == len(input_names), "Duplicate build-input entries")
    actual_inputs = {"README.md"}
    for folder in ("build", "verification"):
        actual_inputs.update(folder + "/" + str(path.relative_to(package / folder))
                             for path in (package / folder).rglob("*")
                             if path.is_file() and path != root / "BUILD-INPUTS.json")
    require(set(input_names) == actual_inputs,
            "Export build/verification file set differs from build-input manifest")
    for row in inputs:
        path = safe_path(package, row["path"])
        require(path.stat().st_size == row["bytes"] and sha(path) == row["sha256"],
                "Build input hash/size mismatch: " + row["path"])
    print(f"PASS: {len(rows)} numerical payload entries; {len(inputs)} clean build inputs.")
    print("Inventory integrity only; run the numerical driver to reproduce its arithmetic checks.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, ValueError) as error:
        raise SystemExit("Certificate integrity check failed: " + str(error))
