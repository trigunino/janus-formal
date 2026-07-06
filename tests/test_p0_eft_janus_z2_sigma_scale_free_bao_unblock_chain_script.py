import unittest

from scripts.run_p0_eft_janus_z2_sigma_scale_free_bao_unblock_chain import build_payload


class ScaleFreeBAOUnblockChainScriptTest(unittest.TestCase):
    def test_live_chain_reports_blocker_without_no_fit_claim(self):
        payload = build_payload()

        self.assertIn("plasma_chain", payload)
        self.assertIn("primitive_obligations", payload)
        self.assertIn("primitive_chi2_chain", payload)
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertNotEqual(payload["primary_blocker"], "none")


if __name__ == "__main__":
    unittest.main()
