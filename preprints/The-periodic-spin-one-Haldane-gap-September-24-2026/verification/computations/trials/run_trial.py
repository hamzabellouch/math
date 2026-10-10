"""Run the preserved polynomial trial at length 72 or 120.

Only the original top-level assignment N=72 is replaced in the executed AST.
All matrix definitions, contractions and original assertions are unchanged.
"""
import argparse
import ast
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import platform
import sys
import time

if not __debug__ or sys.flags.optimize or os.environ.get("PYTHONOPTIMIZE", "0") not in ("", "0"):
    raise SystemExit("Trial verification requires assertions enabled.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--length", type=int, required=True, choices=(72, 120))
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    source = root / "original_trial.py"
    module = ast.parse(source.read_text())
    candidates = [node for node in module.body if isinstance(node, ast.Assign)
                  and any(isinstance(target, ast.Name) and target.id == "N" for target in node.targets)]
    if len(candidates) != 1:
        raise RuntimeError("Expected one original top-level N assignment.")
    assignment = candidates[0]
    if (len(assignment.targets) != 1 or not isinstance(assignment.value, ast.Constant)
            or type(assignment.value.value) is not int or assignment.value.value != 72):
        raise RuntimeError("Expected the original assignment N=72.")
    original_ast = ast.dump(module, include_attributes=False)
    assignment.value.value = args.length
    changed_ast = ast.dump(module, include_attributes=False)
    assignment.value.value = 72
    if ast.dump(module, include_attributes=False) != original_ast:
        raise RuntimeError("Unexpected change to original arithmetic.")
    assignment.value.value = args.length
    if ast.dump(module, include_attributes=False) != changed_ast:
        raise RuntimeError("Length substitution was not reproducible.")
    namespace = {"__name__": "shared_polynomial_trial"}
    printed = io.StringIO()
    started = time.monotonic()
    with contextlib.redirect_stdout(printed):
        exec(compile(module, str(source), "exec"), namespace)
    elapsed = time.monotonic() - started
    num, norm = int(namespace["U"]), int(namespace["V"])
    if list(map(int, printed.getvalue().split())) != [num, norm]:
        raise RuntimeError("Printed and captured full integers differ.")
    margin = -700741*norm - 500000*num
    if norm <= 0 or margin <= 0:
        raise RuntimeError("The exact variational inequality failed.")
    data = {"labels": namespace["labels"],
            "matrices": {str(s): namespace["A"][s].tolist() for s in (-1, 0, 1)}}
    matrix_bytes = (json.dumps(data, separators=(",", ":"))+"\n").encode()
    matrix_path = root / "matrix-data.json"
    if matrix_path.exists() and matrix_path.read_bytes() != matrix_bytes:
        raise RuntimeError("The two lengths did not use the same trial matrices.")
    matrix_path.write_bytes(matrix_bytes)
    record = {"length": args.length, "num": str(num), "norm": str(norm),
              "positive_margin_minus700741V_minus500000U": str(margin),
              "floor_1e12_U_over_V": 10**12*num//norm,
              "matrix_sha256": hashlib.sha256(matrix_bytes).hexdigest(),
              "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
              "runner_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "method": "Original AST with only N=72 replaced by the requested length",
              "assertions_enabled": True, "python": platform.python_version(),
              "wall_seconds": elapsed}
    (root/f"certificate{args.length}.json").write_text(json.dumps(record, indent=2)+"\n")
    (root/f"output{args.length}.txt").write_text(printed.getvalue())
    print(f"PASS: length {args.length}; exact floor {record['floor_1e12_U_over_V']}; {elapsed:.3f} seconds")


if __name__ == "__main__":
    main()
