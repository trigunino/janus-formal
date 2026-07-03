import unittest

from scripts.build_p0_eft_janus_z2_sigma_matter_flux_radial_block_gate import build_payload


class P0EFTJanusZ2SigmaMatterFluxRadialBlockGateTests(unittest.TestCase):
    def test_matter_flux_radial_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["matter_flux_radial_ledger_declared"])
        self.assertTrue(payload["declared"]["matter_flux_route_decision_gate_declared"])
        self.assertTrue(payload["declared"]["transparency_gate_declared"])
        self.assertTrue(payload["declared"]["active_flux_projection_gate_declared"])
        self.assertIn("T_munu", payload["formula"]["flux_one_form"])
        self.assertTrue(payload["declared"]["observational_fit_forbidden"])

    def test_flux_block_waits_for_transparency_or_active_flux(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["transparency_condition_derived"])
        self.assertFalse(payload["closure"]["active_flux_of_a_ready"])
        self.assertFalse(payload["matter_flux_radial_block_reduced"])
        self.assertIn("pass_matter_flux_route_decision_gate", payload["next_required"])
        self.assertIn("pass_matter_flux_transparency_gate_or_reject_transparency", payload["next_required"])
        self.assertIn("pass_matter_flux_active_projection_gate_if_not_transparent", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
