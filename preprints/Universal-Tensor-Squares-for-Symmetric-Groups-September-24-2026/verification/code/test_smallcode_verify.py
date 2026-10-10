"""Fault-injection checks for the writeup's fail-closed verification driver."""
from contextlib import redirect_stderr, redirect_stdout
import io
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import smallcode_verify as verify


VALID_LINES = [
    "partition 0 1 1",
    "dimensions 1000000007 1",
    "square 1000000007 0 1",
    "mixed 1000000007 1",
    "dimensions 1000000009 1",
    "square 1000000009 0 1",
    "mixed 1000000009 1",
]


class DumpValidationTests(unittest.TestCase):
    def compare_output(self, lines):
        result = ("0", 0.0, "\n".join(lines) + "\n", "")
        with patch.object(verify, "bounded_run", return_value=result), redirect_stdout(io.StringIO()):
            verify.compare(1, io.StringIO())

    def test_complete_output_passes(self):
        self.compare_output(VALID_LINES)

    def test_missing_each_record_fails_even_with_zero_child_exit(self):
        for index, line in enumerate(VALID_LINES):
            with self.subTest(record=line), self.assertRaises(verify.VerificationError):
                self.compare_output(VALID_LINES[:index] + VALID_LINES[index+1:])

    def test_missing_final_square_fails(self):
        with self.assertRaises(verify.VerificationError):
            self.compare_output([line for line in VALID_LINES
                                 if not line.startswith("square 1000000009")])

    def test_missing_entire_modulus_fails(self):
        with self.assertRaises(verify.VerificationError):
            self.compare_output([line for line in VALID_LINES if "1000000009" not in line])

    def test_duplicate_each_record_fails(self):
        for line in VALID_LINES:
            with self.subTest(record=line), self.assertRaises(verify.VerificationError):
                self.compare_output(VALID_LINES + [line])

    def test_malformed_or_unexpected_record_fails(self):
        replacements = [
            "unknown 1000000009 1",
            "mixed 1000000021 1",
            "mixed 1000000009",
            "mixed 1000000009 1 1",
            "mixed 1000000009 not_an_integer",
            "mixed 1000000009 -1",
            "mixed 1000000009 1000000009",
            "square 1000000009 1 1",
            "partition 1 1 1",
        ]
        for record in replacements:
            with self.subTest(record=record), self.assertRaises(verify.VerificationError):
                self.compare_output(VALID_LINES[:-1] + [record])

    def test_wrong_coefficient_fails(self):
        with self.assertRaises(verify.VerificationError):
            self.compare_output(VALID_LINES[:-1] + ["mixed 1000000009 0"])


class RunExitTests(unittest.TestCase):
    def invoke_main(self, status):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "runs.log"
            result = (status, 0.01, "", "injected child result\n")
            with patch.object(verify, "bounded_run", return_value=result), \
                    redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                code = verify.main(["runs", "1", "--log", str(log)])
            self.assertIn(f"status={status}", log.read_text())
            return code

    def test_successful_run_returns_zero(self):
        self.assertEqual(self.invoke_main("0"), 0)

    def test_nonzero_child_returns_failure(self):
        for status in ("1", "7", "-6"):
            with self.subTest(status=status):
                self.assertNotEqual(self.invoke_main(status), 0)

    def test_timeout_returns_failure(self):
        self.assertNotEqual(self.invoke_main("TIMEOUT"), 0)

    def test_real_nonzero_child_is_detected(self):
        status, _, _, _ = verify.bounded_run([sys.executable, "-c", "raise SystemExit(7)"], 2)
        self.assertEqual(status, "7")

    def test_real_timeout_is_detected(self):
        status, _, _, _ = verify.bounded_run([sys.executable, "-c", "import time; time.sleep(10)"], 0.05)
        self.assertEqual(status, "TIMEOUT")


if __name__ == "__main__":
    unittest.main(verbosity=2)
