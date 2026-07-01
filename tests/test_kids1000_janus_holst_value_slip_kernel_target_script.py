from __future__ import annotations

import unittest

from scripts.build_kids1000_janus_holst_value_slip_kernel_target import build_payload


class KiDS1000JanusHolstValueSlipKernelTargetTests(unittest.TestCase):
    def test_target_keeps_gate_open_and_blocks_kids_shortcuts(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "value-slip-kernel-target-open")
        self.assertFalse(payload["gate_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertEqual(payload["kids_symptom"]["dominant_pair"], "2-3")
        self.assertFalse(payload["open_inputs"]["algebraic_value_slip_derived"])
        self.assertTrue(any("delta_z=+0.15" in item for item in payload["forbidden_shortcuts"]))

    def test_target_operator_feeds_sigma_not_photoz(self) -> None:
        operator = build_payload()["target_operator"]

        self.assertIn("Sigma_JH", operator["must_feed"])
        self.assertIn("Z_MID_BIN2", operator["must_not_feed"])


if __name__ == "__main__":
    unittest.main()
