from __future__ import annotations

import unittest

from scripts.build_janus_linear_theta_mode_reduction_derivation import build_payload


class JanusLinearThetaModeReductionDerivationTests(unittest.TestCase):
    def test_modal_reduction_is_written_but_open(self) -> None:
        payload = build_payload()
        flags = payload["closure_flags"]

        self.assertEqual(payload["status"], "algebraic-derivation-open")
        self.assertTrue(flags["modal_theta_reduction_written"])
        self.assertFalse(flags["omega_branch_source_derived"])
        self.assertFalse(flags["physical_beta_ready"])
        self.assertFalse(payload["prediction_ready"])

    def test_reduction_contains_sum_source_and_theta_modes(self) -> None:
        reduction = " ".join(build_payload()["modal_reduction"].values())

        self.assertIn("Omega_minus delta_plus", reduction)
        self.assertIn("delta_plus - delta_minus_eff", reduction)
        self.assertIn("theta_sum", " ".join(build_payload()["modal_reduction"].keys()))
        self.assertIn("theta_source", " ".join(build_payload()["modal_reduction"].keys()))
        self.assertIn("theta_plus/theta_minus", reduction)

    def test_blockers_keep_source_qdet_and_l_open(self) -> None:
        blockers = " ".join(build_payload()["blockers"])

        self.assertIn("Omega_plus(a)", blockers)
        self.assertIn("A_J", blockers)
        self.assertIn("Q_det", blockers)
        self.assertIn("L_minus_to_plus", blockers)


if __name__ == "__main__":
    unittest.main()
