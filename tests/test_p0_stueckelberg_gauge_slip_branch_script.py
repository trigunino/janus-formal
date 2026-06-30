from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_gauge_slip_branch import build_payload


class P0GaugeSlipBranchTests(unittest.TestCase):
    def test_zero_stress_check_passes_but_janus_slip_open(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["zero_anisotropic_stress_slip_check_passed"])
        self.assertTrue(decision["gauge_branch_declared"])
        self.assertFalse(decision["janus_slip_equation_derived"])
        self.assertFalse(decision["full_metric_potential_closure"])
        self.assertFalse(payload["prediction_ready"])

    def test_branch_names_metric_and_lensing_potential(self) -> None:
        branch = " ".join(build_payload()["branch"].values())

        self.assertIn("Phi", branch)
        self.assertIn("Psi", branch)
        self.assertIn("Phi_lens=(Phi+Psi)/2", branch)
        self.assertIn("Phi_lens=Phi", branch)

    def test_blockers_keep_anisotropic_stress_open(self) -> None:
        blockers = " ".join(build_payload()["blockers"])

        self.assertIn("cross-sector stress", blockers)
        self.assertIn("transported Pi_minus_to_plus", blockers)
        self.assertIn("vector/tensor perturbations", blockers)


if __name__ == "__main__":
    unittest.main()
