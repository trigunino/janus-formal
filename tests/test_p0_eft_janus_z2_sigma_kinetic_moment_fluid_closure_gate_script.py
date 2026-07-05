import unittest

from scripts.build_p0_eft_janus_z2_sigma_kinetic_moment_fluid_closure_gate import build_payload


class P0EFTJanusZ2SigmaKineticMomentFluidClosureGateTests(unittest.TestCase):
    def test_kinetic_moment_fluid_closure_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["kinetic_moment_fluid_closure_ledger_declared"])
        self.assertTrue(payload["declared"]["stress_energy_moment_formula_declared"])
        self.assertTrue(payload["declared"]["FLRW_isotropy_guard_declared"])
        self.assertTrue(payload["declared"]["distribution_isotropy_anisotropic_stress_gate_declared"])
        self.assertIn("moment_stress", payload["formulas"])

    def test_fluid_closure_waits_for_distribution_eos_and_isotropy(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_distribution_ready"])
        self.assertFalse(payload["closure"]["plus_FLRW_isotropy_derived"])
        self.assertFalse(payload["kinetic_moment_fluid_closure_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(
            payload["primary_blocker"],
            "R_Sigma_solution_certificate",
        )
        self.assertFalse(payload["upstream_frontiers"]["fermion_distribution_of_a"]["gate_passed"])
        self.assertIn("pass_Dirac_equation_of_state_of_a_gate", payload["next_required"])
        self.assertIn("pass_distribution_isotropy_anisotropic_stress_gate", payload["next_required"])
        self.assertIn("feed_result_to_sector_density_pressure_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
