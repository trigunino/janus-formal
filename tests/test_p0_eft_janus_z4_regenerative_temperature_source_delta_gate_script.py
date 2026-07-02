import unittest

from scripts.build_p0_eft_janus_z4_regenerative_temperature_source_delta_gate import build_payload


class P0EFTJanusZ4RegenerativeTemperatureSourceDeltaGateTests(unittest.TestCase):
    def test_temperature_source_delta_regenerates_per_cosmology(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-regenerative-temperature-source-delta-gate")
        self.assertTrue(payload["lambda_frozen"])
        self.assertTrue(payload["no_lambda_retuning"])
        self.assertTrue(payload["no_new_physics"])
        self.assertTrue(payload["source_delta_cache_key_includes_cosmology_hash"])
        self.assertTrue(payload["source_delta_cache_key_includes_lambda_hash"])
        self.assertTrue(payload["W_acoustic_regenerated_per_cosmology"])
        self.assertTrue(payload["kappa_regenerated_per_cosmology"])
        self.assertTrue(payload["deltaPhiDot_plus_deltaPsiDot_regenerated_per_cosmology"])
        self.assertTrue(payload["delta_S_T_Z4_regenerated_per_cosmology"])
        self.assertTrue(payload["no_stale_temperature_source_reuse"])
        self.assertTrue(payload["regenerative_temperature_source_delta_gate_passed"])
        self.assertFalse(payload["local_cosmology_profiling_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
