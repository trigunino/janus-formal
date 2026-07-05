import unittest

from scripts.build_p0_eft_janus_z2_sigma_dirac_scalar_mass_law_gate import build_payload


class P0EFTJanusZ2SigmaDiracScalarMassLawGateTests(unittest.TestCase):
    def test_scalar_mass_law_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["dirac_scalar_mass_law_ledger_declared"])
        self.assertTrue(payload["declared"]["scalar_under_local_Lorentz_criterion_declared"])
        self.assertTrue(payload["declared"]["Z2Sigma_projection_mass_criterion_declared"])
        self.assertIn("mass_term_pm", payload["formulas"])

    def test_scalar_mass_law_closure_remains_blocked(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_mass_term_from_action_derived"])
        self.assertFalse(payload["closure"]["projected_scalar_mass_derived"])
        self.assertFalse(payload["dirac_scalar_mass_law_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "projected_Dirac_action_mass_term")
        self.assertIn("pass_Dirac_mass_term_from_action_gate", payload["next_required"])
        self.assertIn("feed_result_to_Dirac_radial_energy_dispersion_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
