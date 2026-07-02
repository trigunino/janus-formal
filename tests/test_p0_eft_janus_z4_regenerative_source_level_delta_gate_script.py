import unittest

from scripts.build_p0_eft_janus_z4_regenerative_source_level_delta_gate import build_payload


class P0EFTJanusZ4RegenerativeSourceLevelDeltaGateTests(unittest.TestCase):
    def test_source_level_gate_passes_after_temperature_and_pi_sources(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-regenerative-source-level-delta-gate")
        self.assertTrue(payload["effective_gate_passed"])
        self.assertTrue(payload["lambda_frozen"])
        self.assertTrue(payload["no_new_physics"])
        self.assertTrue(payload["delta_S_T_Z4_regenerated_per_cosmology"])
        self.assertTrue(payload["Pi_source_regenerated_per_cosmology"])
        self.assertTrue(payload["photon_polarization_hierarchy_source_regenerated_per_cosmology"])
        self.assertTrue(payload["no_stale_source_delta_reuse"])
        self.assertTrue(payload["full_source_level_z4_delta_regeneration"])
        self.assertFalse(payload["local_cosmology_profiling_allowed"])
        self.assertTrue(payload["strict_source_level_gate_passed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
