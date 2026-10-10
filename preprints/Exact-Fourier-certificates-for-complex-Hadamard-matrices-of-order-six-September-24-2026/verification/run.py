"""Run the exact verifier with assertions and its source checksum checked."""

from hashlib import sha256
from pathlib import Path
import runpy
import sys


def main():
    if sys.flags.optimize:
        raise RuntimeError("Assertions must be enabled: omit -O and PYTHONOPTIMIZE.")
    verifier = Path(__file__).with_name("verify.py")
    expected = "104a7306205b8544c8f913f6afdb59603f2e04a207c9ac592c383b80eb0e2aa9"
    if sha256(verifier.read_bytes()).hexdigest() != expected:
        raise RuntimeError("The verifier differs from the source printed in the paper.")
    runpy.run_path(str(verifier), run_name="__main__")


if __name__ == "__main__":
    main()
