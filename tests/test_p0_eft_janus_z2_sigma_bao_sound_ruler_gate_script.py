import unittest

from scripts.build_p0_eft_janus_z2_sigma_bao_sound_ruler_gate import build_payload


class P0EFTJanusZ2SigmaBAOSoundRulerGateTests(unittest.TestCase):
    def test_bao_sound_ruler_formula_is_declared_without_fitted_planck_rd(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["bao_sound_ruler_lock_closed"])
        self.assertTrue(payload["bao_sound_ruler_formula_ready"])
        self.assertTrue(payload["lock"]["background_equations_derived"])
        self.assertTrue(payload["lock"]["photon_distance_map_derived"])
        self.assertTrue(payload["fitted_planck_rd_forbidden"])
        self.assertTrue(payload["compressed_lcdm_prior_forbidden"])

    def test_bao_sound_ruler_evaluation_waits_for_active_early_plasma(self):
        payload = build_payload()

        self.assertFalse(payload["evaluation"]["H_Z2Sigma_numerical_ready"])
        self.assertFalse(payload["evaluation"]["photon_baryon_sound_speed_ready"])
        self.assertFalse(payload["evaluation"]["drag_epoch_ready"])
        self.assertFalse(payload["bao_sound_ruler_evaluated"])
        self.assertFalse(payload["non_compressed_bao_gate_ready"])
        self.assertIn("derive_drag_epoch_z_d_Z2Sigma", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
