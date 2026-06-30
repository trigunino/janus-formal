from __future__ import annotations

import unittest

from scripts.build_p0_eft_same_l_phase_space_bridge import build_payload, render_markdown


class P0EFTSameLPhaseSpaceBridgeTests(unittest.TestCase):
    def test_liouville_bridge_closes_but_active_measure_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["same_L_bridge_defined_as_cotangent_lift"])
        self.assertTrue(status["liouville_phase_space_jacobian_closed"])
        self.assertFalse(status["mass_shell_measure_closed"])
        self.assertFalse(status["active_B4vol_measure_closed"])
        self.assertFalse(status["prediction_ready_unconditional"])

    def test_cotangent_lift_is_used(self) -> None:
        bridge = build_payload()["bridge"]

        self.assertIn("cotangent_lift", " ".join(bridge.keys()))
        self.assertIn("(D phi^{-1})^T", bridge["cotangent_lift"])

    def test_jacobian_records_liouville_one(self) -> None:
        jacobian = build_payload()["jacobian"]

        self.assertIn("= 1", jacobian["full_phase_space"])
        self.assertIn("B4vol", jacobian["stress_measure"])

    def test_markdown_keeps_measure_open(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("active_B4vol_measure_closed: False", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
