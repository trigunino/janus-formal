from __future__ import annotations

import unittest

from scripts.build_lensing_readiness_report import JSON_PATH, main


class LensingReadinessReportTests(unittest.TestCase):
    def test_metric_potential_gate_is_reported_as_restricted_partial(self) -> None:
        main()
        payload = __import__("json").loads(JSON_PATH.read_text(encoding="utf-8"))
        gates = {row["gate"]: row for row in payload["gates"]}

        self.assertIn("Metric potential / Weyl", gates)
        self.assertEqual(gates["Metric potential / Weyl"]["status"], "restricted partial")
        self.assertTrue(payload["metric_potential_layer"]["restricted_metric_ready"])
        self.assertFalse(payload["metric_potential_layer"]["general_metric_ready"])
        self.assertEqual(payload["metric_potential_layer"]["restricted_numeric_rows"], 2)
        self.assertFalse(payload["metric_potential_layer"]["restricted_numeric_prediction_ready"])

    def test_beta_field_gate_is_diagnostic_only(self) -> None:
        main()
        payload = __import__("json").loads(JSON_PATH.read_text(encoding="utf-8"))
        gates = {row["gate"]: row for row in payload["gates"]}

        self.assertIn("Beta field provenance", gates)
        self.assertEqual(gates["Beta field provenance"]["status"], "diagnostic only")
        self.assertTrue(payload["beta_field_layer"]["pm_calibrated_beta_usable_as_diagnostic"])
        self.assertFalse(payload["beta_field_layer"]["source_derived_beta_available"])
        self.assertFalse(payload["beta_field_layer"]["prediction_ready"])

    def test_lensing_readiness_still_blocks_s8(self) -> None:
        main()
        payload = __import__("json").loads(JSON_PATH.read_text(encoding="utf-8"))

        self.assertIn("Not ready for S8_eff", payload["verdict"])
        self.assertTrue(any(row["blocks_s8"] for row in payload["gates"]))


if __name__ == "__main__":
    unittest.main()
