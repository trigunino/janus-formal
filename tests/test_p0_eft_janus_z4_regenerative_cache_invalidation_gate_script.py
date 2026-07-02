import unittest

from scripts.build_p0_eft_janus_z4_regenerative_cache_invalidation_gate import build_payload


class P0EFTJanusZ4RegenerativeCacheInvalidationGateTests(unittest.TestCase):
    def test_cosmology_mutations_change_hashes_and_spectra(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-regenerative-cache-invalidation-gate")
        self.assertEqual(payload["source_of_spectra"], "regenerated")
        self.assertTrue(payload["cosmology_hash_changes_for_all_mutations"])
        self.assertTrue(payload["spectra_change_for_all_mutations"])
        self.assertTrue(payload["no_stale_csv_reuse"])
        self.assertTrue(payload["cache_key_contains_all_cosmology_params"])
        self.assertTrue(payload["gate_passed"])


if __name__ == "__main__":
    unittest.main()
