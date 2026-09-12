"""Runner structure and failure-record tests with mocked child processes only."""

import contextlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("runner_under_test", ROOT / "verify.py")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


def source_result():
    return {
        "complete": True,
        "box_count": 26,
        "probe_count": 78,
        "boxes": [
            {
                "id": name,
                "complete": True,
                "bands": [{"probe": p, "all_gates": True} for p in (3, 4, 5)],
            }
            for name in ["A"] + [f"{i:02}" for i in range(1, 26)]
        ],
    }


def late_result(index):
    bands = json.loads(
        (ROOT / "support/fields/data/boundary-geometry.json").read_text()
    )["Nbands"]
    return {
        "status": "LATE_BOUNDARY_RANGE_PASS",
        "completed": True,
        "start": index,
        "stop": index + 1,
        "Nbands": bands,
        "bits": 512,
        "rows": [
            {
                "index": index,
                "wide": [{"Nlo": lo, "Nhi": hi} for lo, hi in bands],
                "centers": [{"Nlo": lo, "Nhi": hi} for lo, hi in bands],
            }
        ],
    }


class CompletenessTests(unittest.TestCase):
    def test_every_singleton_late_scope_is_accepted(self):
        indices = []
        for i in range(45, 162):
            result = late_result(i)
            runner.validate(f"late-{i}-{i + 1}", result)
            indices += [row["index"] for row in result["rows"]]
        self.assertEqual(indices, list(range(45, 162)))

    def test_partial_flag_cannot_be_promoted_by_complete_row(self):
        result = late_result(145)
        result["completed"] = False
        with self.assertRaisesRegex(ValueError, "incomplete"):
            runner.validate("late-145-146", result)

    def test_requested_singleton_requires_its_exact_index(self):
        result = late_result(145)
        result["rows"][0]["index"] = 146
        with self.assertRaisesRegex(ValueError, "coverage"):
            runner.validate("late-145-146", result)

    def test_singleton_cannot_omit_a_wide_band(self):
        result = late_result(145)
        result["rows"][0]["wide"].pop()
        with self.assertRaisesRegex(ValueError, "cutoff-band coverage"):
            runner.validate("late-145-146", result)

    def test_singleton_cannot_omit_a_center_band(self):
        result = late_result(145)
        result["rows"][0]["centers"].pop()
        with self.assertRaisesRegex(ValueError, "cutoff-band coverage"):
            runner.validate("late-145-146", result)

    def test_source_counts_do_not_replace_band_completion(self):
        result = source_result()
        runner.validate("source", result)
        result["boxes"][12]["bands"][1]["all_gates"] = False
        with self.assertRaisesRegex(ValueError, "band completeness"):
            runner.validate("source", result)

    def test_source_counts_do_not_replace_catalog_identity(self):
        result = source_result()
        result["boxes"][12]["id"] = "11"
        with self.assertRaisesRegex(ValueError, "identities"):
            runner.validate("source", result)

    def test_direct_sum_requires_both_full_original_sums(self):
        result = {
            "complete": True,
            "bits": 256,
            "checks": [
                {"t": "0", "y": "0", "terms_per_sum": 690950},
                {"t": "1/5", "y": "1", "terms_per_sum": 690950},
            ],
        }
        runner.validate("direct-sums", result)
        result["checks"][1]["terms_per_sum"] -= 1
        with self.assertRaisesRegex(ValueError, "scope"):
            runner.validate("direct-sums", result)

    def test_unsupported_python_refuses_before_any_work(self):
        stderr = io.StringIO()
        with (
            mock.patch.object(runner.sys, "argv", ["verify.py", "--quick"]),
            mock.patch.object(runner.sys, "version_info", (3, 14, 4)),
            mock.patch.object(runner, "load_module") as load,
            contextlib.redirect_stderr(stderr),
        ):
            with self.assertRaises(SystemExit) as error:
                runner.main()
        self.assertEqual(error.exception.code, 1)
        self.assertIn("CPython 3.12", stderr.getvalue())
        load.assert_not_called()


class FailurePreservationTests(unittest.TestCase):
    def test_successful_workspace_is_retained_and_scratch_removed(self):
        with tempfile.TemporaryDirectory(prefix="runner-test-") as directory:
            target = Path(directory) / "records"
            with runner.retain_workspace(target) as scratch:
                (scratch / "stage.json").write_text('{"complete":true}\n')
            self.assertFalse(scratch.exists())
            self.assertEqual((target / "stage.json").read_text(), '{"complete":true}\n')

    def test_aggregate_validation_failure_preserves_partial_records(self):
        with tempfile.TemporaryDirectory(prefix="runner-test-") as directory:
            target = Path(directory) / "records"
            with (
                contextlib.redirect_stderr(io.StringIO()),
                self.assertRaisesRegex(ValueError, "wrong geometry"),
            ):
                with runner.retain_workspace(target) as scratch:
                    (scratch / "partial.json").write_text('{"completed":false}\n')
                    raise ValueError("wrong geometry")
            self.assertFalse(scratch.exists())
            self.assertTrue((target / "partial.json").is_file())
            failure = json.loads((target / "verification.failure.json").read_text())
            self.assertEqual(failure["exception"], "ValueError")
            self.assertIn("wrong geometry", failure["message"])

    def test_interrupt_preserves_available_records(self):
        with tempfile.TemporaryDirectory(prefix="runner-test-") as directory:
            target = Path(directory) / "records"
            with (
                contextlib.redirect_stderr(io.StringIO()),
                self.assertRaises(KeyboardInterrupt),
            ):
                with runner.retain_workspace(target) as scratch:
                    (scratch / "started.json").write_text("{}")
                    raise KeyboardInterrupt()
            failure = json.loads((target / "verification.failure.json").read_text())
            self.assertEqual(failure["exception"], "KeyboardInterrupt")
            self.assertTrue((target / "started.json").is_file())

    def test_nonzero_child_is_recorded_once_without_stream_truncation(self):
        stdout = "first-output-marker\n" + "x" * 6000
        stderr = "first-error-marker\n" + "y" * 6000
        completed = subprocess.CompletedProcess(["mock-child"], -11, stdout, stderr)
        with tempfile.TemporaryDirectory(prefix="runner-test-") as directory:
            tmp = Path(directory)
            printed = io.StringIO()
            with (
                mock.patch.object(
                    runner.subprocess, "run", return_value=completed
                ) as run,
                contextlib.redirect_stderr(printed),
                self.assertRaises(ValueError),
            ):
                runner.run_process("native", ["mock-child"], {}, tmp)
            run.assert_called_once()
            failure = json.loads((tmp / "native.failure.json").read_text())
            self.assertEqual(failure["returncode"], -11)
            self.assertEqual(failure["stdout"], stdout)
            self.assertEqual(failure["stderr"], stderr)
            self.assertIn("first-output-marker", printed.getvalue())
            self.assertIn("first-error-marker", printed.getvalue())

    def test_timeout_preserves_byte_streams_and_exception(self):
        error = subprocess.TimeoutExpired(
            ["mock-child"], 5, output=b"partial stdout", stderr=b"partial stderr"
        )
        with tempfile.TemporaryDirectory(prefix="runner-test-") as directory:
            tmp = Path(directory)
            with (
                mock.patch.object(runner.subprocess, "run", side_effect=error) as run,
                contextlib.redirect_stderr(io.StringIO()),
                self.assertRaises(subprocess.TimeoutExpired),
            ):
                runner.run_process("timeout", ["mock-child"], {}, tmp, timeout=5)
            run.assert_called_once()
            failure = json.loads((tmp / "timeout.failure.json").read_text())
            self.assertEqual(failure["exception"], "TimeoutExpired")
            self.assertEqual(failure["stdout"], "partial stdout")
            self.assertEqual(failure["stderr"], "partial stderr")

    def test_launch_error_is_preserved(self):
        with tempfile.TemporaryDirectory(prefix="runner-test-") as directory:
            tmp = Path(directory)
            with (
                mock.patch.object(
                    runner.subprocess,
                    "run",
                    side_effect=FileNotFoundError("missing child"),
                ),
                contextlib.redirect_stderr(io.StringIO()),
                self.assertRaises(FileNotFoundError),
            ):
                runner.run_process("launch", ["mock-child"], {}, tmp)
            failure = json.loads((tmp / "launch.failure.json").read_text())
            self.assertEqual(failure["exception"], "FileNotFoundError")
            self.assertEqual(failure["command"], ["mock-child"])


if __name__ == "__main__":
    unittest.main()
