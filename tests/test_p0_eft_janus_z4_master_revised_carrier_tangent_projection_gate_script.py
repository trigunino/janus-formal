import unittest

from scripts.build_p0_eft_janus_z4_master_revised_carrier_tangent_projection_gate import build_payload


class P0EFTJanusZ4MasterRevisedCarrierTangentProjectionGateTests(unittest.TestCase):
    def test_revised_master_source_passes_carrier_tangent_projection(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-revised-carrier-tangent-projection-gate")
        self.assertTrue(payload["source_level_v2_passed"])
        self.assertLess(payload["parallel_fraction"], 0.7)
        self.assertGreater(payload["perpendicular_fraction"], 0.3)
        self.assertEqual(payload["dominant_tangent_direction"], "A_s")
        self.assertTrue(payload["carrier_threshold_passed"])
        self.assertTrue(payload["nontrivial_signal_preserved"])
        self.assertFalse(payload["downstream_patch_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["observed_Planck_rerun_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
