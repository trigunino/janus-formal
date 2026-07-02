import unittest

from scripts.build_p0_eft_janus_z4_two_sector_boltzmann_variables_gate import build_payload


class P0EFTJanusZ4TwoSectorBoltzmannVariablesGateTests(unittest.TestCase):
    def test_two_sector_variables_declared_without_shortcuts(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-two-sector-boltzmann-variables-gate")
        self.assertTrue(payload["plus_sector_declared"])
        self.assertTrue(payload["minus_sector_declared"])
        self.assertIn("delta_plus", payload["plus_sector_variables"])
        self.assertIn("delta_minus", payload["minus_sector_variables"])
        self.assertIn("Phi_plus", payload["metric_variables"])
        self.assertIn("Phi_minus", payload["metric_variables"])
        self.assertIn("P_Z4_plus_obs", payload["projection_variables"])
        self.assertTrue(payload["z4_projection_declared"])
        self.assertTrue(payload["coupling_matrix_declared"])
        self.assertTrue(payload["sign_convention_declared"])
        self.assertTrue(payload["rho_eff_shortcut_forbidden"])
        self.assertTrue(payload["direct_Cl_patch_forbidden"])
        self.assertTrue(payload["raw_toy_LOS_forbidden"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertTrue(payload["carrier_tangent_projection_required_before_promotion"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
