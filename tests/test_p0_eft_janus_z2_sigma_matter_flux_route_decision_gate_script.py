import unittest

from scripts.build_p0_eft_janus_z2_sigma_matter_flux_route_decision_gate import build_payload


class P0EFTJanusZ2SigmaMatterFluxRouteDecisionGateTests(unittest.TestCase):
    def test_route_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["matter_flux_route_ledger_declared"])
        self.assertTrue(payload["declared"]["transparency_route_declared"])
        self.assertTrue(payload["declared"]["active_projection_route_declared"])
        self.assertTrue(payload["declared"]["route_choice_by_fit_forbidden"])

    def test_route_is_not_decided_without_derivation(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["transparency_derived"])
        self.assertFalse(payload["closure"]["active_flux_projection_ready"])
        self.assertFalse(payload["closure"]["matter_flux_route_decided"])
        self.assertFalse(payload["matter_flux_route_decision_ready"])
        self.assertIn("choose_route_from_derivation_not_observational_fit", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
