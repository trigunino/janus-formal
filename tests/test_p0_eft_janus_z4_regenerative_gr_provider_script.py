import unittest

from scripts.build_p0_eft_janus_z4_regenerative_gr_provider import build_payload


class P0EFTJanusZ4RegenerativeGRProviderTests(unittest.TestCase):
    def test_regenerative_gr_provider_contract(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-regenerative-gr-provider")
        self.assertEqual(payload["source_of_spectra"], "regenerated")
        self.assertTrue(payload["backend_regenerative"])
        self.assertFalse(payload["z4_sector_enabled"])
        self.assertEqual(payload["lambda_T"], 0.0)
        self.assertEqual(payload["lambda_E"], 0.0)
        self.assertTrue(payload["finite_tt_te_ee_pp_produced"])
        self.assertTrue(payload["ell_grid_strictly_increasing"])
        self.assertTrue(payload["positive_auto_spectra"])
        self.assertTrue(payload["cache_keys_complete"])
        self.assertTrue(payload["no_csv_fixed_theory_vector"])
        self.assertTrue(payload["regenerative_gr_provider_ready"])


if __name__ == "__main__":
    unittest.main()
