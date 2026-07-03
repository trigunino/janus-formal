import unittest

from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_well_posedness_gate import build_payload


class P0EFTJanusZ2SigmaCoupledRadiusFluxWellPosednessGateTests(unittest.TestCase):
    def test_well_posedness_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["well_posedness_ledger_declared"])
        self.assertIn("R_Sigma(a) in a declared radial regularity class", payload["unknown_space"])
        self.assertTrue(payload["declared"]["no_independent_flux_shortcut"])

    def test_well_posedness_remains_blocked_until_proved(self):
        payload = build_payload()

        self.assertFalse(payload["proof_obligations"]["local_existence_proved"])
        self.assertFalse(payload["proof_obligations"]["local_uniqueness_proved"])
        self.assertFalse(payload["well_posedness_ready"])
        self.assertFalse(payload["coupled_system_well_posed"])
        self.assertIn("coupled_system_well_posed = false", payload["current_frontier"])


if __name__ == "__main__":
    unittest.main()
