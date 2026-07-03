import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_flrw_obligation_gate import build_payload


class P0EFTJanusZ2SigmaCountertermFLRWObligationGateTests(unittest.TestCase):
    def test_counterterm_method_is_ready_from_sigma_closure(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["counterterm_method_ready"])
        self.assertTrue(payload["method"]["sigma_supported_counterterm_unique"])
        self.assertIn("delta S_ct", payload["formulas"]["counterterm_stress"])

    def test_active_flrw_counterterm_stress_remains_open(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["counterterm_FLRW_stress_reduced"])
        self.assertFalse(payload["closure"]["counterterm_rho_p_of_a_ready"])
        self.assertFalse(payload["counterterm_FLRW_closure_ready"])
        self.assertIn("vary_counterterm_with_respect_to_FLRW_induced_metric", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
