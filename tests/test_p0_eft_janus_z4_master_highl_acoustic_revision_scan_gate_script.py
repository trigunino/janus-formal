import unittest

from scripts.build_p0_eft_janus_z4_master_highl_acoustic_revision_scan_gate import build_payload


class P0EFTJanusZ4MasterHighLAcousticRevisionScanGateTests(unittest.TestCase):
    def test_revision_scan_finds_upstream_non_tangent_highl_reduction(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-highl-acoustic-revision-scan-gate")
        self.assertEqual(payload["observed_failure_class"], "high_l_acoustic_shape_failure")
        self.assertTrue(payload["revision_found"])
        best = payload["best_revision"]
        self.assertLess(best["parallel_fraction"], 0.7)
        self.assertLess(best["highl_reduction_factor"], 0.5)
        self.assertGreater(best["max_abs_fractional_delta"], 0.05)
        self.assertFalse(payload["downstream_patch_allowed"])
        self.assertFalse(payload["observed_planck_rerun_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
