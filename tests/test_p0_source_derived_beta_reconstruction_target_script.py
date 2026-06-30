from __future__ import annotations

import unittest

from scripts.build_p0_source_derived_beta_reconstruction_target import build_payload


class P0SourceDerivedBetaReconstructionTargetTests(unittest.TestCase):
    def test_target_is_open_and_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "reconstruction-target-open")
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["blockers"]["source_derived_beta_available"])

    def test_reconstruction_chain_uses_theta_velocity_l_and_beta(self) -> None:
        steps = " ".join(build_payload()["reconstruction_steps"])

        self.assertIn("delta_plus", steps)
        self.assertIn("theta_s", steps)
        self.assertIn("v_s(k,a)=i k theta_s/k^2", steps)
        self.assertIn("L_minus_to_plus", steps)
        self.assertIn("source_derived_janus_dynamics", steps)

    def test_acceptance_checks_forbid_fit_and_pm_provenance(self) -> None:
        checks = " ".join(build_payload()["acceptance_checks"])

        self.assertIn("never sigma8/S8 fitted", checks)
        self.assertIn("Q_det", checks)
        self.assertIn("K/Q_cross", checks)
        self.assertIn("not physical provenance", checks)


if __name__ == "__main__":
    unittest.main()
