import unittest

from scripts.build_p0_eft_janus_z4_master_ansatz_revision_scan_gate import build_payload


class P0EFTJanusZ4MasterAnsatzRevisionScanGateTests(unittest.TestCase):
    def test_scan_is_internal_and_blocks_observational_use(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-ansatz-revision-scan-gate")
        self.assertIn("best_ansatz", payload)
        self.assertIn("best_parallel_fraction", payload)
        self.assertGreaterEqual(payload["best_parallel_fraction"], 0.0)
        self.assertTrue(payload["scan_is_internal_not_observational_fit"])
        self.assertFalse(payload["lambda_retuning_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
