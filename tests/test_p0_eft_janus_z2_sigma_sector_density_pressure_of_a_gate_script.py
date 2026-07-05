import unittest

from scripts.build_p0_eft_janus_z2_sigma_sector_density_pressure_of_a_gate import build_payload


class P0EFTJanusZ2SigmaSectorDensityPressureOfAGateTests(unittest.TestCase):
    def test_sector_density_pressure_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["sector_density_pressure_ledger_declared"])
        self.assertTrue(payload["declared"]["Dirac_equation_of_state_gate_declared"])
        self.assertTrue(payload["declared"]["kinetic_moment_fluid_closure_gate_declared"])
        self.assertIn("dirac_equation_of_state", payload["upstream_frontiers"])
        self.assertIn("kinetic_moment_fluid_closure", payload["upstream_frontiers"])
        self.assertIn("continuity_plus", payload["formulas"])
        self.assertTrue(payload["declared"]["observational_fit_forbidden"])

    def test_sector_density_pressure_waits_for_eos_and_normalization(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_equation_of_state_derived"])
        self.assertFalse(payload["closure"]["plus_initial_normalization_derived"])
        self.assertFalse(payload["sector_density_pressure_of_a_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(
            payload["primary_blocker"],
            "R_Sigma_solution_certificate",
        )
        self.assertIn("pass_Dirac_equation_of_state_of_a_gate", payload["next_required"])
        self.assertIn("pass_kinetic_moment_fluid_closure_gate", payload["next_required"])
        self.assertIn("derive_sector_normalizations_from_action_or_topology", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
