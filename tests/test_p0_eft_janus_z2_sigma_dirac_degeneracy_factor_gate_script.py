import unittest

from scripts.build_p0_eft_janus_z2_sigma_dirac_degeneracy_factor_gate import build_payload


class P0EFTJanusZ2SigmaDiracDegeneracyFactorGateTests(unittest.TestCase):
    def test_degeneracy_factor_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["dirac_degeneracy_factor_ledger_declared"])
        self.assertTrue(payload["declared"]["Dirac_internal_degrees_declared"])
        self.assertTrue(payload["declared"]["no_degeneracy_fit"])
        self.assertIn("generic_factor", payload["formulas"])

    def test_degeneracy_factor_waits_for_spinor_projection(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_spinor_bundle_ready"])
        self.assertFalse(payload["closure"]["projected_degeneracy_factor_ready"])
        self.assertFalse(payload["dirac_degeneracy_factor_ready"])
        self.assertIn("pass_spinor_bundle_projection_gate", payload["next_required"])
        self.assertIn("feed_result_to_Dirac_thermal_occupation_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
