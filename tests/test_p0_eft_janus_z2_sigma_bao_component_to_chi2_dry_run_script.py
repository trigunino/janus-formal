import unittest

from scripts.build_p0_eft_janus_z2_sigma_bao_component_to_chi2_dry_run import build_payload


class P0EFTJanusZ2SigmaBAOComponentToChi2DryRunTests(unittest.TestCase):
    def test_component_to_chi2_path_runs_without_official_promotion(self):
        payload = build_payload()

        self.assertTrue(payload["dry_run_only"])
        self.assertFalse(payload["official_bao_evaluation"])
        self.assertTrue(payload["component_manifest_writer_exercised"])
        self.assertTrue(payload["strict_background_manifest_exercised"])
        self.assertTrue(payload["strict_flrw_manifest_exercised"])
        self.assertTrue(payload["strict_early_plasma_manifest_exercised"])
        self.assertTrue(payload["strict_three_manifest_merge_exercised"])
        self.assertTrue(payload["active_manifest_pipeline_exercised"])
        self.assertTrue(payload["official_chi2_calculator_exercised"])
        self.assertFalse(payload["compressed_planck_lcdm_rd_used"])
        self.assertFalse(payload["archived_z4_reuse_used"])
        self.assertGreater(payload["data_points"], 0)
        self.assertGreater(payload["rd_Z2Sigma_mpc"], 0.0)
        self.assertGreater(payload["chi2_DESI_DR2_BAO_dry_run"], 0.0)


if __name__ == "__main__":
    unittest.main()
