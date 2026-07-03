import unittest

from scripts.build_p0_eft_janus_z2_sigma_matter_flux_transparency_gate import build_payload


class P0EFTJanusZ2SigmaMatterFluxTransparencyGateTests(unittest.TestCase):
    def test_transparency_criteria_are_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["transparency_criteria_declared"])
        self.assertTrue(payload["criteria"]["normal_matter_current_gate_declared"])
        self.assertTrue(payload["criteria"]["projected_Dirac_normal_current_gate_declared"])
        self.assertTrue(payload["criteria"]["bulk_stress_normal_flux_cancellation_gate_declared"])
        self.assertIn("F_a^Z2Sigma", payload["sufficient_condition"])
        self.assertTrue(payload["criteria"]["observational_fit_forbidden"])

    def test_active_transparency_is_not_derived_yet(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["no_normal_matter_current_derived"])
        self.assertFalse(payload["closure"]["active_Sigma_transparency_derived"])
        self.assertFalse(payload["active_sigma_transparency_ready"])
        self.assertIn("pass_normal_matter_current_gate", payload["next_required"])
        self.assertIn("pass_projected_Dirac_normal_current_gate", payload["next_required"])
        self.assertIn("pass_bulk_stress_normal_flux_cancellation_gate", payload["next_required"])
        self.assertIn("if_transparency_fails_compute_active_flux_F_a_of_a", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
