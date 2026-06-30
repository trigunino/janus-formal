from __future__ import annotations

import unittest

from scripts.build_p0_pressure_pi_omega_extension_blocker import build_payload


class P0PressurePiOmegaExtensionBlockerTests(unittest.TestCase):
    def test_extension_is_blocked_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "extension-blocked")
        self.assertTrue(payload["rank_one_dust_omega_closure_insufficient"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertTrue(payload["closure_gates"]["rank_one_dust_omega_closed"])
        self.assertFalse(payload["closure_gates"]["scalar_absorption_allowed"])

    def test_remaining_terms_cover_pressure_pi_and_cross_pressure(self) -> None:
        terms = " ".join(build_payload()["remaining_tensor_terms"])

        self.assertIn("p h^{mu nu}", terms)
        self.assertIn("D p", terms)
        self.assertIn("projector transport", terms)
        self.assertIn("Pi^{mu nu}", terms)
        self.assertIn("divergence", terms)
        self.assertIn("equation of state", terms)
        self.assertIn("cross-pressure", terms)

    def test_shortcuts_forbid_scalar_q_absorption(self) -> None:
        shortcuts = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("scalar Q_det", shortcuts)
        self.assertIn("scalar Q_cross", shortcuts)
        self.assertIn("Omega_u u=0", shortcuts)
        self.assertIn("rank-one dust", shortcuts)
        self.assertIn("scalar calibration", shortcuts)


if __name__ == "__main__":
    unittest.main()
