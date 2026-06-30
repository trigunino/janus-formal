from __future__ import annotations

import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

import scripts.build_qcross_four_velocity_target as target
from scripts.build_qcross_four_velocity_target import build_payload


class QCrossFourVelocityTargetScriptTests(unittest.TestCase):
    def test_payload_separates_required_layers_without_closure_claim(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["physics_closed"])
        self.assertEqual(
            set(payload["sections"]),
            {
                "equal_projection",
                "local_velocity_bridge",
                "missing_global_four_velocity_closure",
                "pm_usage_conditions",
            },
        )
        self.assertTrue(payload["sections"]["equal_projection"]["admissible_now"])
        self.assertFalse(
            payload["sections"]["missing_global_four_velocity_closure"][
                "admissible_now"
            ]
        )
        self.assertIn("not closed", payload["verdict"])

    def test_main_writes_json_and_markdown_reports(self) -> None:
        with TemporaryDirectory() as tmpdir:
            old_report_path = target.REPORT_PATH
            old_json_path = target.JSON_PATH
            try:
                target.REPORT_PATH = Path(tmpdir) / "qcross.md"
                target.JSON_PATH = Path(tmpdir) / "qcross.json"

                target.main()

                payload = json.loads(target.JSON_PATH.read_text(encoding="utf-8"))
                report = target.REPORT_PATH.read_text(encoding="utf-8")
            finally:
                target.REPORT_PATH = old_report_path
                target.JSON_PATH = old_json_path

        self.assertFalse(payload["physics_closed"])
        self.assertIn("missing_global_four_velocity_closure", report)
        self.assertIn("PM outputs", report)


if __name__ == "__main__":
    unittest.main()
