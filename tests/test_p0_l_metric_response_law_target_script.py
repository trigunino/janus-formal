from __future__ import annotations

import unittest

from scripts.build_p0_l_metric_response_law_target import build_payload


class P0LMetricResponseLawTargetTests(unittest.TestCase):
    def test_symmetric_response_closed_lorentz_gauge_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "symmetric-l-response-closed-lorentz-gauge-open")
        self.assertTrue(payload["compatibility_variation_closed"])
        self.assertTrue(payload["symmetric_l_response_closed"])
        self.assertFalse(payload["antisymmetric_lorentz_gauge_closed"])
        self.assertTrue(payload["free_l_branch_rejected_as_default"])
        self.assertTrue(payload["same_l_for_k_qcross_required"])
        self.assertFalse(payload["delta_g_l_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_cover_compatibility_variation_and_gauge(self) -> None:
        text = " ".join(row["formula"] + row["status"] for row in build_payload()["law_rows"])

        self.assertIn("L^T g_plus", text)
        self.assertIn("delta(g^{-1})", text)
        self.assertIn("Sym(L^{-1} delta L)", text)
        self.assertIn("Anti(L^{-1} delta L)", text)
        self.assertIn("Omega_ab=-Omega_ba", text)
        self.assertIn("K transport and Q_cross", text)


if __name__ == "__main__":
    unittest.main()
