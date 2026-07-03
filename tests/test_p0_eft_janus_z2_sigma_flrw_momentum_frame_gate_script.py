import unittest

from scripts.build_p0_eft_janus_z2_sigma_flrw_momentum_frame_gate import build_payload


class P0EFTJanusZ2SigmaFLRWMomentumFrameGateTests(unittest.TestCase):
    def test_flrw_momentum_frame_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["flrw_momentum_frame_ledger_declared"])
        self.assertTrue(payload["declared"]["comoving_momentum_declared"])
        self.assertTrue(payload["declared"]["isotropic_momentum_norm_declared"])
        self.assertIn("momentum_norm", payload["formulas"])

    def test_flrw_momentum_frame_closure_remains_blocked(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_coframe_pullback_ready"])
        self.assertFalse(payload["closure"]["projected_FLRW_momentum_frame_derived"])
        self.assertFalse(payload["flrw_momentum_frame_ready"])
        self.assertIn("feed_result_to_Dirac_radial_energy_dispersion_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
