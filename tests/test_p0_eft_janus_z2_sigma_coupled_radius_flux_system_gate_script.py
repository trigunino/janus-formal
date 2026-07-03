import unittest

from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_system_gate import build_payload


class P0EFTJanusZ2SigmaCoupledRadiusFluxSystemGateTests(unittest.TestCase):
    def test_coupled_system_ledger_and_equations_are_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["coupled_radius_flux_ledger_declared"])
        self.assertIn("R_Sigma(a)", payload["coupled_unknowns"])
        self.assertIn("flux", payload["coupled_equations"])
        self.assertTrue(payload["declared"]["no_independent_flux_shortcut_declared"])

    def test_solution_remains_blocked_until_well_posed_and_solved(self):
        payload = build_payload()

        self.assertFalse(payload["system"]["coupled_system_well_posed"])
        self.assertFalse(payload["solution"]["coupled_system_solved"])
        self.assertFalse(payload["coupled_radius_flux_system_ready"])
        self.assertFalse(payload["coupled_radius_flux_solution_ready"])
        self.assertIn("coupled_system_well_posed = false", payload["current_frontier"])


if __name__ == "__main__":
    unittest.main()
