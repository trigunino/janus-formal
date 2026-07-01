from __future__ import annotations

import unittest

from scripts.build_kids1000_janus_holst_kernel_closure_decision import build_payload


class KiDS1000JanusHolstKernelClosureDecisionTests(unittest.TestCase):
    def test_payload_freezes_candidate_without_prediction_promotion(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "diagnostic-kernel-candidate-frozen")
        self.assertEqual(payload["promotion_decision"], "do-not-promote-to-prediction")
        self.assertFalse(payload["prediction_ready"])
        self.assertIn("kernel_variant", payload["frozen_diagnostic_candidate"])


if __name__ == "__main__":
    unittest.main()
