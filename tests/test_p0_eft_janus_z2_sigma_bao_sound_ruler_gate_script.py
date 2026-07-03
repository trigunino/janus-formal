import unittest

from scripts.build_p0_eft_janus_z2_sigma_bao_sound_ruler_gate import build_payload


class P0EFTJanusZ2SigmaBAOSoundRulerGateTests(unittest.TestCase):
    def test_bao_sound_ruler_is_derived_without_fitted_planck_rd(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["bao_sound_ruler_lock_closed"])
        self.assertTrue(payload["bao_sound_ruler_derived"])
        self.assertTrue(payload["lock"]["background_equations_derived"])
        self.assertTrue(payload["lock"]["photon_distance_map_derived"])
        self.assertTrue(payload["fitted_planck_rd_forbidden"])
        self.assertTrue(payload["compressed_lcdm_prior_forbidden"])
        self.assertTrue(payload["non_compressed_bao_gate_ready"])


if __name__ == "__main__":
    unittest.main()
