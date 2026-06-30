from __future__ import annotations

import unittest

from scripts.build_bianchi_lorentz_residual_reduction import build_payload


class BianchiLorentzResidualReductionTests(unittest.TestCase):
    def test_lorentz_dust_substitution_reduces_but_does_not_close(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["algebraic_substitution_closed"])
        self.assertTrue(payload["residuals_reduced"])
        self.assertFalse(payload["residuals_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_product_rule_terms_and_connection_force_are_explicit(self) -> None:
        payload = build_payload()
        residuals = " ".join(row["residual"] for row in payload["reduced_residuals"])

        self.assertIn("D_minus_nu(rho_minus u_{-to+}^nu)", residuals)
        self.assertIn("u_{-to+}^nu D_minus_nu u_{-to+}^mu", residuals)
        self.assertIn("C^mu_{nu a} rho_minus", residuals)
        self.assertIn("- C^mu_{nu a} rho_plus", residuals)

    def test_l_derivative_and_both_residuals_remain_required(self) -> None:
        payload = build_payload()
        requirements = " ".join(payload["closure_requirements"])

        self.assertIn("D L_minus_to_plus", requirements)
        self.assertIn("D L_plus_to_minus", requirements)
        self.assertIn("R_plus^mu=0", requirements)
        self.assertIn("R_minus^mu=0", requirements)

    def test_qcross_scalar_shortcut_is_forbidden(self) -> None:
        forbidden = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("scalar Q_cross", forbidden)
        self.assertIn("do not drop C^mu", forbidden)


if __name__ == "__main__":
    unittest.main()
