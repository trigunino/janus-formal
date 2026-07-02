import unittest

from scripts.build_p0_eft_janus_z4_master_source_level_regeneration_gate import build_payload


class P0EFTJanusZ4MasterSourceLevelRegenerationGateTests(unittest.TestCase):
    def test_sources_are_regenerated_from_single_master_generator(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-source-level-regeneration-gate")
        self.assertTrue(payload["master_ansatz_revision_scan_passed"])
        self.assertEqual(payload["selected_master_ansatz"], "localized_transition")
        self.assertLess(payload["selected_master_parallel_fraction"], 0.7)
        self.assertTrue(payload["U_Z4_regenerated"])
        self.assertTrue(payload["S_T_Z4_regenerated_from_U_Z4"])
        self.assertTrue(payload["S_E_Z4_regenerated_from_U_Z4"])
        self.assertTrue(payload["S_lens_Z4_regenerated_from_U_Z4"])
        self.assertTrue(payload["all_sources_share_same_U_Z4_hash"])
        self.assertFalse(payload["independent_downstream_source_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])


if __name__ == "__main__":
    unittest.main()
