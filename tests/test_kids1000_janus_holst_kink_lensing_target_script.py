from __future__ import annotations

import unittest

from scripts.build_kids1000_janus_holst_kink_lensing_target import build_payload


class KiDS1000JanusHolstKinkLensingTargetTests(unittest.TestCase):
    def test_kink_target_is_open_and_value_slip_disabled(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "kink-lensing-target-open")
        self.assertEqual(payload["gate"], "kink_lensing_projection")
        self.assertFalse(payload["value_slip_status"]["can_enable_value_slip"])
        self.assertFalse(payload["gate_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_target_operator_avoids_green_and_kids_shortcuts(self) -> None:
        operator = build_payload()["target_operator"]

        self.assertIn("Delta(partial_n(Psi-Phi))", operator["input"])
        self.assertIn("not algebraic eta_slip", operator["feeds"])
        self.assertIn("Z_MID_BIN2", operator["does_not_use"])


if __name__ == "__main__":
    unittest.main()
