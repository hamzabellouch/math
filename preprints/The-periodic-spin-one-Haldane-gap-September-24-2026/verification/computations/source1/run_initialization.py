"""Execute only the original scalar suffix, without repeating matrix calculations."""
from pathlib import Path
import runpy

if not __debug__:
    raise SystemExit("Assertions must be enabled; do not use python -O.")

root = Path(__file__).resolve().parent
source = (root / "original-computation.py").read_text()
marker = "\nM=[[0]*4+"
if source.count(marker) != 1:
    raise RuntimeError("The preserved source must contain exactly one scalar suffix.")
namespace = runpy.run_path(str(root / "thermal-definitions.py"))
suffix = source[source.index(marker) + 1:]
exec(compile(suffix, "original-computation.py:scalar-suffix", "exec"), namespace)
