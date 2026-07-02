import unittest

from scripts.build_p0_eft_janus_z4_solver_input_manifest_gate import build_payload


class P0EFTJanusZ4SolverInputManifestGateTests(unittest.TestCase):
    def test_manifest_blocks_hidden_inputs_and_ls_calibration(self):
        payload = build_payload()

        self.assertFalse(payload["solver_input_manifest_passed"])
        self.assertFalse(payload["z4_observed_planck_interpretation_allowed"])
        self.assertTrue(payload["blockers"]["hidden_default_inputs"])
        self.assertTrue(payload["blockers"]["global_LS_channel_calibration"])
        self.assertTrue(payload["blockers"]["z4_initial_mode_unspecified"])
        self.assertTrue(payload["blockers"]["minus_microphysics_unspecified"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
