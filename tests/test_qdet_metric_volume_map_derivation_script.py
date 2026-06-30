from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_qdet_metric_volume_map_derivation import build_payload, write_reports


class QDetMetricVolumeMapDerivationTests(unittest.TestCase):
    def test_explicit_names_avoid_det4_dust_volume_ambiguity(self) -> None:
        payload = build_payload()
        definitions = payload["definitions"]
        distinctions = {row["name"]: row for row in payload["distinctions"]}

        self.assertIn("qdet_4volume_ratio", definitions)
        self.assertIn("qdet_dust_volume_ratio", definitions)
        self.assertIn("sqrt(-g_minus)", definitions["qdet_4volume_ratio"])
        self.assertIn("sqrt(h_minus)", definitions["qdet_dust_volume_ratio"])
        self.assertTrue(distinctions["qdet_4volume_ratio"]["includes_lapse"])
        self.assertFalse(distinctions["qdet_dust_volume_ratio"]["includes_lapse"])
        self.assertNotEqual(
            definitions["qdet_4volume_ratio"],
            definitions["qdet_dust_volume_ratio"],
        )

    def test_no_raw_scale_ratio_lensing_amplitude_is_accepted(self) -> None:
        payload = build_payload()
        forbidden = payload["forbidden_lensing_amplitudes"]

        self.assertEqual(payload["accepted_raw_scale_ratio_lensing_amplitudes"], [])
        self.assertTrue(all(row["accepted"] is False for row in forbidden))
        self.assertIn(
            "raw_flrw_scale_ratio",
            {row["name"] for row in forbidden},
        )
        self.assertIn(
            "optical/lensing amplitude",
            " ".join(payload["density_map"]["not_allowed"]),
        )

    def test_prediction_remains_blocked_until_source_equations_fix_convention(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["source_equation_convention_fixed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertIn("source equations", " ".join(payload["missing_for_closure"]))
        self.assertIn("not Q_cross", payload["verdict"])

    def test_write_reports_emits_json_and_markdown(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            report_path = Path(tmpdir) / "qdet_map.md"
            json_path = Path(tmpdir) / "qdet_map.json"

            write_reports(report_path, json_path)

            payload = json.loads(json_path.read_text(encoding="utf-8"))
            markdown = report_path.read_text(encoding="utf-8")

        self.assertFalse(payload["prediction_ready"])
        self.assertIn("qdet_4volume_ratio", markdown)
        self.assertIn("Forbidden Lensing Amplitudes", markdown)


if __name__ == "__main__":
    unittest.main()
