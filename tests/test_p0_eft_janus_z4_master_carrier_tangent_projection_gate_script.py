import unittest

from scripts.build_p0_eft_janus_z4_master_carrier_tangent_projection_gate import build_payload


class P0EFTJanusZ4MasterCarrierTangentProjectionGateTests(unittest.TestCase):
    def test_master_projection_reports_thresholds_without_planck(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-carrier-tangent-projection-gate")
        self.assertTrue(payload["master_to_observable_map_gate_passed"])
        self.assertTrue(payload["all_channels_derived_from_same_U_Z4"])
        self.assertIn("cl_tt", payload["channels_projected"])
        self.assertGreaterEqual(payload["parallel_fraction"], 0.0)
        self.assertGreaterEqual(payload["perpendicular_fraction"], 0.0)
        self.assertIn("dominant_tangent_direction", payload)
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
