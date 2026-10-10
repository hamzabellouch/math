#!/usr/bin/env python3
"""Focused failure-mode tests for the reproduction wrapper, not its algebra."""

from contextlib import redirect_stdout
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("reproduce", HERE / "reproduce.py")
reproduce = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(reproduce)


class ReproductionGuardTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original = HERE / "original"
        cls.records = reproduce.verify_archive(cls.original)
        cls.bodies = reproduce.verify_extraction(cls.original)
        cls.tables = (HERE.parent.parent / "build" / "appendices" / "tables.tex").read_bytes()

    def copied_archive(self, directory):
        target = Path(directory) / "original"
        shutil.copytree(self.original, target)
        return target

    def test_same_length_changes_to_input_code_table_and_expected_result_fail(self):
        names = (
            "certificate-inputs.txt", "checks/exact-source.py", "checks/exact-table-I.txt",
            "checks/exact-results.json",
        )
        with tempfile.TemporaryDirectory() as directory:
            original = self.copied_archive(directory)
            for name in names:
                with self.subTest(file=name):
                    path = original / name
                    raw = path.read_bytes()
                    path.write_bytes(bytes([raw[0] ^ 1]) + raw[1:])
                    with self.assertRaisesRegex(reproduce.CheckFailure, "SHA-256 mismatch"):
                        reproduce.verify_archive(original)
                    path.write_bytes(raw)

    def test_editing_file_and_updating_manifest_cannot_redefine_trusted_output(self):
        with tempfile.TemporaryDirectory() as directory:
            original = self.copied_archive(directory)
            altered = b"changed source\n"
            (original / "checks" / "exact-source.py").write_bytes(altered)
            path = original / "final-integrity.json"
            manifest = json.loads(path.read_bytes())
            for record in manifest["files"]:
                if record["path"] == "checks/exact-source.py":
                    record.update(bytes=len(altered), sha256=reproduce.digest(altered))
            path.write_text(json.dumps(manifest), encoding="utf-8")
            with self.assertRaisesRegex(reproduce.CheckFailure, "manifest SHA-256 mismatch"):
                reproduce.verify_archive(original)

    def test_modified_typeset_coefficient_and_block_header_fail(self):
        mutations = (
            (b"f 000 172575762", b"f 000 172575763"),
            (b"@ 0 none I", b"@ 0 none B"),
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "tables.tex"
            for before, after in mutations:
                with self.subTest(before=before):
                    self.assertIn(before, self.tables)
                    path.write_bytes(self.tables.replace(before, after, 1))
                    with self.assertRaisesRegex(reproduce.CheckFailure, "differs from literal source"):
                        reproduce.verify_typeset_tables(path, self.bodies)

    def test_typeset_delimiter_or_environment_damage_fails(self):
        reproduce.verify_typeset_tables(
            HERE.parent.parent / "build" / "appendices" / "tables.tex", self.bodies
        )
        for before, after in (
            (b"\\endgroup", b"\\endgroupDamaged"),
            (reproduce.VERBATIM_BEGIN, b"\\begin{verbatim}"),
        ):
            with self.subTest(before=before), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "tables.tex"
                path.write_bytes(self.tables.replace(before, after, 1))
                with self.assertRaises(reproduce.CheckFailure):
                    reproduce.verify_typeset_tables(path, self.bodies)

    def test_independent_input_prefix_excludes_the_source_fence(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "certificate-inputs.txt"
            path.write_text("~~~\na\n~~~\n~~~\nb\n~~~\n~~~\nsource\n", encoding="utf-8")
            with self.assertRaisesRegex(reproduce.CheckFailure, "exactly two fenced tables"):
                reproduce.independent_input_digest(path)

    def test_historical_result_comparison_validates_current_digests(self):
        current_digests = {"input_sha256": "1" * 64, "source_sha256": "2" * 64}
        historical = {"input_sha256": "a" * 64, "source_sha256": "b" * 64, "value": [1, 2]}
        current = {**current_digests, "value": [1, 2]}
        encode = lambda value: (json.dumps(value, indent=2) + "\n").encode("ascii")
        expected = encode(historical)
        self.assertEqual(
            reproduce.compare_historical_result(encode(current), expected, current_digests),
            reproduce.digest(expected),
        )
        for field, value in (("input_sha256", "3" * 64), ("value", [1, 3]), ("extra", 1)):
            with self.subTest(field=field):
                changed = dict(current)
                changed[field] = value
                with self.assertRaises(reproduce.CheckFailure):
                    reproduce.compare_historical_result(encode(changed), expected, current_digests)

    def test_successful_child_without_new_output_cannot_reuse_stale_output(self):
        with tempfile.TemporaryDirectory() as directory:
            stage = Path(directory)
            (stage / "checks").mkdir()
            (stage / "checks" / "probe.py").write_text("pass\n", encoding="utf-8")
            (stage / "checks" / "result.json").write_bytes(b"old result\n")
            records = {"checks/result.json": {"bytes": 11, "sha256": reproduce.digest(b"old result\n")}}
            with redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(reproduce.CheckFailure, "Missing regular file"):
                    reproduce.run_check(stage, "probe.py", "result.json", False, records)

    def test_child_assertions_remain_enabled_with_optimized_environment(self):
        with tempfile.TemporaryDirectory() as directory:
            stage = Path(directory)
            (stage / "checks").mkdir()
            (stage / "checks" / "probe.py").write_text(
                "assert False, 'assertions are active'\n", encoding="utf-8"
            )
            with patch.dict(os.environ, {"PYTHONOPTIMIZE": "2"}), redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(reproduce.CheckFailure, "assertions are active"):
                    reproduce.run_check(stage, "probe.py", "unused.json", False, {})

    def test_optimized_cli_rejects_tampering_from_unrelated_working_directory(self):
        with tempfile.TemporaryDirectory(prefix="wrapper guards with spaces ") as directory:
            package = Path(directory) / "relocated writeup"
            checks = package / "checks"
            checks.mkdir(parents=True)
            shutil.copyfile(HERE / "reproduce.py", checks / "reproduce.py")
            original = self.copied_archive(checks)
            path = original / "certificate-inputs.txt"
            raw = path.read_bytes()
            path.write_bytes(bytes([raw[0] ^ 1]) + raw[1:])
            environment = os.environ.copy()
            environment["PYTHONOPTIMIZE"] = "2"
            result = subprocess.run(
                [sys.executable, "-O", "-B", str(checks / "reproduce.py")],
                cwd=directory, env=environment,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(b"SHA-256 mismatch", result.stderr)

    def test_independent_source_freeze_outputs_and_provenance_are_pinned(self):
        reference = HERE.parent / "independent-certificate"
        reproduce.verify_independent(reference)
        with tempfile.TemporaryDirectory() as directory:
            copied = Path(directory) / "independent"
            shutil.copytree(reference, copied, ignore=shutil.ignore_patterns("__pycache__"))
            for name in (
                "engine.py", "bounds.py", "compare_oracle.py", "engine.py.first-frozen",
                "output/coefficients.json", "output/results.json", "output/oracle-comparison.json",
                "provenance.json",
            ):
                with self.subTest(file=name):
                    path = copied / name
                    raw = path.read_bytes()
                    path.write_bytes(bytes([raw[0] ^ 1]) + raw[1:])
                    with self.assertRaisesRegex(reproduce.CheckFailure, "SHA-256 mismatch"):
                        reproduce.verify_independent(copied)
                    path.write_bytes(raw)

    def test_independent_bootstrap_loads_siblings_with_assertions_enabled(self):
        with tempfile.TemporaryDirectory(prefix="independent imports with spaces ") as directory:
            stage = Path(directory)
            (stage / "bounds.py").write_text(
                "import sys\nassert sys.flags.optimize == 0\nvalue = 'local import passed'\n",
                encoding="utf-8",
            )
            script = stage / "engine.py"
            script.write_text("from bounds import value\nprint(value)\n", encoding="utf-8")
            with patch.dict(os.environ, {"PYTHONOPTIMIZE": "2"}), redirect_stdout(io.StringIO()):
                stdout = reproduce.run_program(reproduce.independent_command(script), stage, "probe")
            self.assertEqual(stdout, b"local import passed\n")
            (stage / "bounds.py").write_text("assert False, 'sibling assertions active'\n", encoding="utf-8")
            with patch.dict(os.environ, {"PYTHONOPTIMIZE": "2"}), redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(reproduce.CheckFailure, "sibling assertions active"):
                    reproduce.run_program(reproduce.independent_command(script), stage, "probe")

    def test_independent_zero_exit_without_new_outputs_cannot_pass(self):
        reference = HERE.parent / "independent-certificate"
        records = reproduce.verify_independent(reference)
        with tempfile.TemporaryDirectory() as directory:
            stage = Path(directory) / "independent"
            with patch.object(reproduce, "run_program", return_value=b""), redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(reproduce.CheckFailure, "Missing regular file"):
                    reproduce.run_independent(reference, stage, self.original, records)
            self.assertFalse((stage / "output" / "coefficients.json").exists())

    def test_comparison_allows_only_validated_path_change(self):
        preserved = HERE.parent / "independent-certificate" / "output" / "oracle-comparison.json"
        report = json.loads(preserved.read_bytes())
        with tempfile.TemporaryDirectory(prefix="comparison relocation ") as directory:
            oracle = Path(directory) / "original" / "checks" / "exact-results.json"
            generated = Path(directory) / "comparison.json"
            report["oracle_path"] = str(oracle.resolve())
            generated.write_text(json.dumps(report), encoding="utf-8")
            self.assertRegex(reproduce.verify_comparison(generated, preserved, oracle), r"^[0-9a-f]{64}$")
            unmarked = Path(directory) / "unmarked-preserved.json"
            old_report = json.loads(preserved.read_bytes())
            old_report["oracle_path"] = "unmarked path"
            unmarked.write_text(json.dumps(old_report), encoding="utf-8")
            with self.assertRaisesRegex(reproduce.CheckFailure, "explicitly mark"):
                reproduce.verify_comparison(generated, unmarked, oracle)
            for key, value in (
                ("oracle_path", str(oracle.with_name("other.json"))),
                ("passed", False), ("passed", 1), ("coefficient_mismatches", 1),
                ("oracle_sha256", "0" * 64), ("unexpected_field", "unexpected"),
            ):
                with self.subTest(field=key, value=value):
                    changed = dict(report)
                    changed[key] = value
                    generated.write_text(json.dumps(changed), encoding="utf-8")
                    with self.assertRaises(reproduce.CheckFailure):
                        reproduce.verify_comparison(generated, preserved, oracle)

    def test_bad_fresh_independent_output_fails_before_oracle_comparison(self):
        reference = HERE.parent / "independent-certificate"
        records = reproduce.verify_independent(reference)
        with tempfile.TemporaryDirectory() as directory:
            stage = Path(directory) / "independent"
            def fake_run(command, directory, label):
                if label == "independent full interior expansion":
                    output = stage / "output"
                    output.mkdir()
                    raw = (reference / "output" / "coefficients.json").read_bytes()
                    (output / "coefficients.json").write_bytes(bytes([raw[0] ^ 1]) + raw[1:])
                    shutil.copyfile(reference / "output" / "results.json", output / "results.json")
                elif label == "independent coefficient comparison":
                    self.fail("Comparison must not run after a fresh coefficient mismatch")
                return b""
            with patch.object(reproduce, "run_program", side_effect=fake_run), redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(reproduce.CheckFailure, "SHA-256 mismatch"):
                    reproduce.run_independent(reference, stage, self.original, records)


if __name__ == "__main__":
    unittest.main()
