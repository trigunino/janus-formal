import unittest

from scripts.build_p0_eft_janus_z4_regenerative_z4_delta_per_cosmology_gate import build_payload


class P0EFTJanusZ4RegenerativeZ4DeltaPerCosmologyGateTests(unittest.TestCase):
    def test_effective_deltas_regenerate_but_strict_gate_blocks(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-regenerative-z4-delta-per-cosmology-gate")
        self.assertEqual(payload["source_of_spectra"], "regenerated")
        self.assertEqual(payload["z4_delta_source"], "effective_regenerated_per_cosmology")
        self.assertTrue(payload["lambda_hash_includes_lambda_T_lambda_E"])
        self.assertTrue(payload["z4_delta_cache_key_includes_cosmology_hash"])
        self.assertTrue(payload["effective_z4_spectrum_deltas_regenerated_per_cosmology"])
        self.assertTrue(payload["no_stale_delta_reuse"])
        self.assertFalse(payload["delta_S_T_Z4_regenerated_per_cosmology"])
        self.assertFalse(payload["Pi_source_regenerated_per_cosmology"])
        self.assertFalse(payload["full_source_level_z4_delta_regeneration"])
        self.assertFalse(payload["z4_deltas_regenerated_per_cosmology"])
        self.assertFalse(payload["local_cosmology_profiling_allowed"])
        self.assertTrue(payload["effective_gate_passed"])
        self.assertFalse(payload["strict_gate_passed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
