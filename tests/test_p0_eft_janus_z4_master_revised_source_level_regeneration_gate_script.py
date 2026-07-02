import unittest

from scripts.build_p0_eft_janus_z4_master_revised_source_level_regeneration_gate import (
    build_payload,
    build_revised_source_payload,
)


class P0EFTJanusZ4MasterRevisedSourceLevelRegenerationGateTests(unittest.TestCase):
    def test_selected_revision_regenerates_all_sources_from_revised_u_z4(self):
        payload = build_payload()
        source = build_revised_source_payload()

        self.assertEqual(payload["status"], "janus-z4-master-revised-source-level-regeneration-gate")
        self.assertTrue(payload["revision_scan_passed"])
        self.assertEqual(payload["selected_revision"], "shared_U_norm_silk_guard")
        self.assertLess(payload["selected_revision_parallel_fraction"], 0.7)
        self.assertLess(payload["selected_revision_highl_reduction_factor"], 0.5)
        self.assertEqual(source["version"], payload["source_level_version"])
        self.assertTrue(payload["U_Z4_revised_from_selected_revision"])
        self.assertTrue(payload["S_T_Z4_regenerated_from_revised_U_Z4"])
        self.assertTrue(payload["S_E_Z4_regenerated_from_revised_U_Z4"])
        self.assertTrue(payload["Pi_Z4_regenerated_from_revised_U_Z4"])
        self.assertTrue(payload["all_revised_sources_share_same_U_Z4_hash"])
        self.assertFalse(payload["downstream_patch_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["observed_Planck_rerun_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
