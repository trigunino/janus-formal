import unittest

from scripts.build_p0_eft_janus_z4_two_sector_conservation_bianchi_gate import build_payload


class P0EFTJanusZ4TwoSectorConservationBianchiGateTests(unittest.TestCase):
    def test_two_sector_conservation_blocks_unconserved_projection(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-two-sector-conservation-bianchi-gate")
        self.assertTrue(payload["variables_gate_passed"])
        self.assertTrue(payload["plus_sector_conservation_declared"])
        self.assertTrue(payload["minus_sector_conservation_declared"])
        self.assertTrue(payload["exchange_terms_declared"])
        self.assertTrue(payload["exchange_terms_explicit_zero"])
        self.assertTrue(payload["Q_plus_plus_projected_Q_minus_zero"])
        self.assertTrue(payload["continuity_equation_plus_available"])
        self.assertTrue(payload["Euler_equation_plus_available"])
        self.assertTrue(payload["shear_equation_plus_available_or_closure_declared"])
        self.assertTrue(payload["continuity_equation_minus_available"])
        self.assertTrue(payload["Euler_equation_minus_available"])
        self.assertTrue(payload["shear_equation_minus_available_or_closure_declared"])
        self.assertTrue(payload["coupling_matrix_conservation_compatible"])
        self.assertTrue(payload["projection_matrix_conservation_compatible"])
        self.assertTrue(payload["Bianchi_residual_declared"])
        self.assertTrue(payload["Bianchi_residual_guard"])
        self.assertTrue(payload["GR_limit_recovered"])
        self.assertTrue(payload["negative_sector_sign_policy_declared"])
        self.assertTrue(payload["negative_density_as_thermodynamic_density"])
        self.assertTrue(payload["gravitational_coupling_sign_declared"])
        self.assertTrue(payload["negative_gravitational_sign_does_not_imply_negative_thermodynamic_density"])
        self.assertTrue(payload["rho_eff_shortcut_forbidden"])
        self.assertTrue(payload["effective_rho_collapse_forbidden"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
