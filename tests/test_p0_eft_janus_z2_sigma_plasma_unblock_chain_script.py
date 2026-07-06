import unittest

from scripts.run_p0_eft_janus_z2_sigma_plasma_unblock_chain import build_payload


class PlasmaUnblockChainScriptTest(unittest.TestCase):
    def test_live_chain_reports_blocker_without_no_fit_claim(self):
        payload = build_payload()

        self.assertIn("density_chain", payload)
        self.assertIn("si_baryon_density", payload)
        self.assertIn("saha_history", payload)
        self.assertIn("saha_inputs", payload)
        self.assertIn("early_plasma_manifest", payload)
        self.assertIn("thomson_drag", payload)
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertNotEqual(payload["primary_blocker"], "none")


if __name__ == "__main__":
    unittest.main()
