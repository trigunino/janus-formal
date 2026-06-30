from __future__ import annotations

import unittest

from scripts.diagnose_restricted_metric_weyl_chain import build_payload


class RestrictedMetricWeylChainTests(unittest.TestCase):
    def test_rows_are_restricted_metric_ready_but_not_predictive(self) -> None:
        payload = build_payload(grid=16)

        self.assertFalse(payload["prediction_ready"])
        self.assertEqual({row["case"] for row in payload["rows"]}, {"negative_cluster", "negative_hole"})
        self.assertTrue(all(row["restricted_metric_ready"] for row in payload["rows"]))
        self.assertFalse(any(row["prediction_ready"] for row in payload["rows"]))

    def test_outputs_include_weyl_trace_free_statistics(self) -> None:
        row = build_payload(grid=16)["rows"][0]

        self.assertIn("center_convergence", row)
        self.assertIn("gamma1_rms", row)
        self.assertIn("gamma2_rms", row)
        self.assertIn("weyl_trace_free_rms", row)

    def test_boundary_keeps_survey_and_tensor_lensing_blocked(self) -> None:
        boundary = build_payload(grid=16)["boundary"]

        self.assertIn("comoving scalar zero-Pi branch", boundary)
        self.assertIn("survey and tensor-lensing predictions remain blocked", boundary)


if __name__ == "__main__":
    unittest.main()
