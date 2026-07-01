from __future__ import annotations

import unittest

from scripts.build_kids1000_cosebis_operator_report import build_payload


class KiDS1000CosebisOperatorReportTests(unittest.TestCase):
    def test_operator_is_ready_but_chi2_is_blocked_without_janus_xi(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["operator_ready"])
        self.assertFalse(payload["janus_xi_prediction_ready"])
        self.assertFalse(payload["chi2_ready"])
        self.assertEqual(payload["scale_cut_en_dimension"], 75)
        self.assertIn("xi_plus", " ".join(payload["next_required"]))


if __name__ == "__main__":
    unittest.main()
