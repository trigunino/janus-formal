from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_qdet_metric_volume_target import build_payload, write_reports


class QDetMetricVolumeTargetTests(unittest.TestCase):
    def test_branch_statuses_keep_physics_open(self) -> None:
        payload = build_payload()
        branches = {row["branch"]: row for row in payload["branches"]}

        self.assertEqual(branches["positive_effective"]["status"], "admissible-diagnostic")
        self.assertEqual(
            branches["negative_proper"]["status"], "admissible-derivation-target"
        )
        self.assertEqual(branches["flrw_raw_forbidden"]["status"], "forbidden")
        self.assertFalse(payload["closes_tensor_lensing"])
        self.assertIn("does not close", payload["verdict"])

    def test_missing_tensor_lensing_requirements_are_explicit(self) -> None:
        payload = build_payload()
        missing = " ".join(payload["missing_for_tensor_lensing"])

        self.assertIn("positive optical volume", missing)
        self.assertIn("cross-sector stress projection", missing)
        self.assertIn("without fitting Q_det", missing)

    def test_write_reports_emits_json_and_markdown(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            report_path = Path(tmpdir) / "qdet.md"
            json_path = Path(tmpdir) / "qdet.json"

            write_reports(report_path, json_path)

            payload = json.loads(json_path.read_text(encoding="utf-8"))
            markdown = report_path.read_text(encoding="utf-8")

        self.assertEqual(len(payload["branches"]), 3)
        self.assertIn("flrw_raw_forbidden", markdown)
        self.assertIn("Missing For Tensor Lensing", markdown)


if __name__ == "__main__":
    unittest.main()
