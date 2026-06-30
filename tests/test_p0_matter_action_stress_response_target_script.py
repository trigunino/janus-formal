from __future__ import annotations

import unittest

from scripts.build_p0_matter_action_stress_response_target import build_payload


class P0MatterActionStressResponseTargetTests(unittest.TestCase):
    def test_matter_action_response_is_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "matter-action-stress-response-open")
        self.assertFalse(payload["dust_response_closed"])
        self.assertTrue(payload["dust_metric_stress_response_target_available"])
        self.assertFalse(payload["perfect_fluid_response_closed"])
        self.assertFalse(payload["anisotropic_response_closed"])
        self.assertTrue(payload["same_phi_l_required"])
        self.assertFalse(payload["stress_response_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_branches_cover_dust_pressure_and_pi(self) -> None:
        text = " ".join(row["stress"] + row["needed_response"] for row in build_payload()["matter_branches"])

        self.assertIn("rho u^mu u^nu", text)
        self.assertIn("rho+p", text)
        self.assertIn("Pi^{mu nu}", text)
        self.assertIn("delta_g Pi", text)

    def test_forbids_freeze_and_scalar_absorption(self) -> None:
        shortcuts = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("freeze T", shortcuts)
        self.assertIn("Q_cross/Q_det", shortcuts)
        self.assertIn("dust response", shortcuts)
        self.assertIn("FLRW scalar", shortcuts)


if __name__ == "__main__":
    unittest.main()
