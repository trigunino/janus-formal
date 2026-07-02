import unittest

from scripts.build_p0_eft_janus_z4_two_sector_linear_evolution_closure_gate import build_payload


class P0EFTJanusZ4TwoSectorLinearEvolutionClosureGateTests(unittest.TestCase):
    def test_linear_evolution_closes_without_spectra_or_planck(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-two-sector-linear-evolution-closure-gate")
        self.assertTrue(payload["initial_mode_gate_passed"])
        self.assertTrue(payload["state_vector_declared"])
        self.assertIn("delta_plus", payload["state_vector"])
        self.assertIn("delta_minus", payload["state_vector"])
        self.assertTrue(payload["linear_evolution_operator_declared"])
        self.assertTrue(payload["plus_fluid_rows_evolved"])
        self.assertTrue(payload["minus_fluid_rows_evolved"])
        self.assertTrue(payload["plus_metric_constraints_evolved"])
        self.assertTrue(payload["minus_metric_constraints_evolved"])
        self.assertTrue(payload["projection_rows_evolved"])
        self.assertTrue(payload["coupling_matrix_enters_operator"])
        self.assertTrue(payload["exchange_terms_respect_bianchi_gate"])
        self.assertTrue(payload["constraint_preservation_guard"])
        self.assertTrue(payload["superhorizon_regular_evolution_guard"])
        self.assertTrue(payload["GR_limit_evolution_recovered"])
        self.assertTrue(payload["hidden_sector_not_forced_to_plus"])
        self.assertTrue(payload["rho_eff_shortcut_forbidden"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertTrue(payload["eigenmode_stability_required_next"])
        self.assertFalse(payload["source_level_regeneration_allowed"])
        self.assertFalse(payload["carrier_tangent_projection_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
