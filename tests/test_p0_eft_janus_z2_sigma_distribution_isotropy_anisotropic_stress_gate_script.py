import unittest

from scripts.build_p0_eft_janus_z2_sigma_distribution_isotropy_anisotropic_stress_gate import build_payload


class P0EFTJanusZ2SigmaDistributionIsotropyAnisotropicStressGateTests(unittest.TestCase):
    def test_distribution_isotropy_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["distribution_isotropy_ledger_declared"])
        self.assertTrue(payload["declared"]["projected_isotropy_criterion_declared"])
        self.assertTrue(payload["declared"]["anisotropic_stress_tensor_declared"])
        self.assertIn("anisotropic_stress", payload["formulas"])

    def test_distribution_isotropy_closure_remains_blocked(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_momentum_isotropy_derived"])
        self.assertFalse(payload["closure"]["projected_anisotropic_stress_zero_derived"])
        self.assertFalse(payload["distribution_isotropy_closure_ready"])
        self.assertIn("pass_Dirac_Fermi_Dirac_isotropy_gate", payload["next_required"])
        self.assertIn("pass_radial_occupation_projection_gate", payload["next_required"])
        self.assertIn("feed_result_to_kinetic_moment_fluid_closure_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
