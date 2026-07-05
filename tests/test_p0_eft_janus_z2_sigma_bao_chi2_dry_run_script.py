import unittest

from scripts.build_p0_eft_janus_z2_sigma_bao_chi2_dry_run import build_payload


class P0EFTJanusZ2SigmaBAOChi2DryRunTests(unittest.TestCase):
    def test_dry_run_computes_vector_but_blocks_official_evaluation(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["dry_run_only"])
        self.assertFalse(payload["official_bao_evaluation"])
        self.assertEqual(payload["data_points"], 13)
        self.assertEqual(payload["prediction_vector_length"], 13)
        self.assertGreater(payload["dry_run_chi2"], 0.0)
        self.assertFalse(payload["official_chi2_allowed"])

    def test_dry_run_does_not_use_forbidden_sources(self):
        payload = build_payload()

        self.assertFalse(payload["compressed_planck_lcdm_rd_used"])
        self.assertFalse(payload["archived_z4_reuse_used"])
        self.assertFalse(payload["uses_active_derived_H_Z2Sigma"])
        self.assertFalse(payload["uses_active_derived_rd_Z2Sigma"])


if __name__ == "__main__":
    unittest.main()
