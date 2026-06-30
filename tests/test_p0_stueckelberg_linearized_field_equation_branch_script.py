from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_linearized_field_equation_branch import build_payload


class P0LinearizedFieldEquationBranchTests(unittest.TestCase):
    def test_normalization_checked_but_branch_not_closed(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["linearized_00_poisson_normalization_checked"])
        self.assertFalse(decision["janus_linearized_field_equation_derived"])
        self.assertFalse(decision["gauge_assumption_closed"])
        self.assertFalse(decision["source_identity_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_branch_contains_linearized_00_and_poisson_limit(self) -> None:
        branch = " ".join(build_payload()["branch"].values())

        self.assertIn("delta G00_plus", branch)
        self.assertIn("2 Delta Psi_plus", branch)
        self.assertIn("Delta Psi_plus = 4 pi G rho_eff_plus", branch)
        self.assertIn("rho_plus-rho_minus_eff", branch)

    def test_blockers_keep_gauge_slip_and_source_open(self) -> None:
        blockers = " ".join(build_payload()["blockers"])

        self.assertIn("derive the scalar gauge", blockers)
        self.assertIn("Phi_lens_plus=(Phi+Psi)", blockers)
        self.assertIn("delta S00_plus", blockers)
        self.assertIn("full tensor lensing", blockers)


if __name__ == "__main__":
    unittest.main()
