import unittest

from scripts.build_p0_eft_janus_z2_sigma_drag_epoch_bracket_finder_gate import build_payload


class P0EFTJanusZ2SigmaDragEpochBracketFinderGateTests(unittest.TestCase):
    def test_bracket_finder_declares_active_inputs_only(self):
        payload = build_payload()

        self.assertTrue(payload["drag_epoch_bracket_finder_ready"])
        self.assertTrue(payload["requires_active_H_Z2Sigma"])
        self.assertTrue(payload["requires_active_Gamma_drag_Z2Sigma"])
        self.assertTrue(payload["requires_active_z_grid"])
        self.assertFalse(payload["uses_planck_lcdm_drag_epoch_fit"])
        self.assertFalse(payload["uses_archived_z4_inputs"])
        self.assertFalse(payload["z_d_values_ready"])


if __name__ == "__main__":
    unittest.main()
