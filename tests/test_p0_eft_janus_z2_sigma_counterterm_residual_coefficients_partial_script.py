import unittest

from scripts.derive_p0_eft_janus_z2_sigma_counterterm_residual_coefficients_partial import (
    build_payload,
)


class P0EFTJanusZ2SigmaCountertermResidualCoefficientsPartialTests(unittest.TestCase):
    def test_torsion_coefficient_reduces_on_active_torsionless_branch(self):
        payload = build_payload()
        coeff = payload["coefficients"]

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(coeff["torsionless_sigma_branch"])
        self.assertTrue(coeff["R_T_A_ready"])
        self.assertTrue(coeff["R_chi_partial_R_chi_ready"])
        self.assertFalse(coeff["R_chi_ready"])
        self.assertFalse(coeff["full_coefficient_expansion_explicit"])
        self.assertEqual(coeff["still_requires"], ["R_h^{ab}", "R_K^{ab}", "R_chi"])
        self.assertEqual(
            coeff["still_requires_for_radial_contractions"],
            ["R_h^{ab} q_ab", "R_K^{ab} q_ab"],
        )
        self.assertFalse(coeff["fitted_counterterm_coefficient_used"])


if __name__ == "__main__":
    unittest.main()
