import unittest

from scripts.build_p0_eft_janus_z2_background_observational_endpoint import build_payload


class BackgroundObservationalEndpointTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = build_payload()

    def test_endpoint_runs(self):
        payload = self.payload
        self.assertEqual(payload["status"], "janus-z2-background-observational-endpoint")
        self.assertEqual(payload["datasets"]["SN"], "Pantheon+ full covariance")
        self.assertEqual(payload["datasets"]["BAO"], "DESI DR2 Gaussian BAO covariance")

    def test_current_janus_endpoint_is_boundary_limited(self):
        janus = self.payload["janus_endpoint"]
        self.assertTrue(janus["at_grid_boundary"])
        self.assertTrue(self.payload["gr_limit_edge_preferred"])

    def test_current_endpoint_does_not_recommend_branch_3(self):
        self.assertFalse(self.payload["continuation_to_branch_3_recommended"])
        self.assertGreater(self.payload["delta_chi2_janus_minus_best_baseline"], 0.0)


if __name__ == "__main__":
    unittest.main()
