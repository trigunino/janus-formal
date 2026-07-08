import unittest

from scripts.build_p0_eft_janus_z2_alpha_observational_fit_gate import build_payload


class AlphaObservationalFitGateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = build_payload()

    def test_fit_gate_runs(self):
        payload = self.payload

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["observable_sector_parameter"], "q0")
        self.assertFalse(payload["alpha_dimensional_map_ready"])
        self.assertFalse(payload["fit_policy"]["no_fit_claim"])
        self.assertEqual(payload["primary_observational_endpoint"], "SN_full_cov_plus_BAO")
        self.assertTrue(payload["datasets"]["SN"]["full_covariance_used"])

    def test_combined_fit_is_boundary_limited_currently(self):
        combined = self.payload["best_fit"]["SN_full_cov_plus_BAO"]

        self.assertLess(combined["q0"], 0.0)
        self.assertTrue(combined["at_grid_boundary"])
        self.assertEqual(
            self.payload["classification"],
            "observational_sector_selection_to_gr_limit_boundary_limited",
        )

    def test_bao_status_is_not_promoted(self):
        self.assertEqual(
            self.payload["janus_bao_status"],
            "rejected_in_current_background_proxy",
        )
        self.assertFalse(self.payload["full_covariance_required_before_final_claim"])


if __name__ == "__main__":
    unittest.main()
