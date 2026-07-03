import unittest

from scripts.build_p0_eft_janus_z2_sigma_matter_flux_radius_acyclicity_gate import build_payload


class P0EFTJanusZ2SigmaMatterFluxRadiusAcyclicityGateTests(unittest.TestCase):
    def test_acyclicity_ledger_declares_no_independent_flux_shortcut(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["matter_flux_radius_acyclicity_ledger_declared"])
        self.assertTrue(payload["declared"]["coupled_radius_flux_system_imported"])
        self.assertTrue(payload["declared"]["independent_flux_source_for_radius_forbidden"])
        self.assertIn("forbidden", payload["policy"])

    def test_matter_flux_cannot_enter_radius_solution_yet(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["transparency_acyclic_ready"])
        self.assertFalse(payload["closure"]["coupled_radius_flux_system_ready"])
        self.assertFalse(payload["matter_flux_radius_acyclic_route_ready"])
        self.assertIn("transparency_acyclic_ready = false", payload["current_frontier"])


if __name__ == "__main__":
    unittest.main()
