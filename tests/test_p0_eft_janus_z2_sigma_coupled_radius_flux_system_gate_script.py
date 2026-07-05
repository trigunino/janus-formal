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
        self.assertTrue(payload["declared"]["coupled_radius_flux_function_space_imported"])
        self.assertTrue(payload["declared"]["coupled_radius_flux_well_posedness_imported"])
        self.assertEqual(
            payload["primary_blocker"],
            "R_Sigma_solution_certificate",
        )

    def test_solution_remains_blocked_until_well_posed_and_solved(self):
        payload = build_payload()

        self.assertFalse(payload["system"]["function_space_ready_for_well_posedness"])
        self.assertFalse(payload["system"]["well_posedness_ready"])
        self.assertFalse(payload["system"]["coupled_system_well_posed"])
        self.assertFalse(payload["solution"]["coupled_system_solved"])
        self.assertFalse(payload["coupled_radius_flux_system_ready"])
        self.assertFalse(payload["coupled_radius_flux_solution_ready"])
        self.assertFalse(payload["upstream_frontiers"]["function_space"]["ready"])
        self.assertFalse(payload["upstream_frontiers"]["well_posedness"]["ready"])
        self.assertEqual(
            payload["upstream_frontiers"]["function_space"]["primary_blocker"],
            "R_Sigma_solution_certificate",
        )
        self.assertEqual(
            payload["upstream_frontiers"]["well_posedness"]["primary_blocker"],
            "R_Sigma_solution_certificate",
        )
        self.assertIn(
            "embedding_trace_map_continuous = false",
            payload["well_posedness_reduction_frontier"][
                "remaining_function_space_blockers"
            ],
        )
        self.assertIn("coupled_system_well_posed = false", payload["current_frontier"])


if __name__ == "__main__":
    unittest.main()
