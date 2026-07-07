import unittest

from scripts.run_p0_eft_janus_z2_bimetric_sigma_transfer_pipeline import build_payload


class BimetricSigmaTransferPipelineTests(unittest.TestCase):
    def test_live_pipeline_reports_first_blocker_without_shortcut(self):
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["first_blocker"]["name"], "density_normalization")
        self.assertIn("local_N_occ_R_curv", payload["first_blocker"]["routes"])
        self.assertIn("published_alpha_global_energy", payload["first_blocker"]["routes"])
        self.assertTrue(payload["no_rustine_policy"]["no_rho_eff_collapse"])


if __name__ == "__main__":
    unittest.main()
