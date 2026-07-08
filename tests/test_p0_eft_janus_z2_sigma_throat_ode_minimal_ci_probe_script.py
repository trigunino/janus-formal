import unittest

from scripts.build_p0_eft_janus_z2_sigma_throat_ode_minimal_ci_probe import build_payload


class P0EFTJanusZ2SigmaThroatODEMinimalCIProbeTests(unittest.TestCase):
    def test_probe_reports_unique_normalized_shape_and_scale_degeneracy(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["normalized_solution_unique_under_minimal_CI"])
        self.assertFalse(payload["R0_unique"])
        self.assertTrue(payload["R0_scale_degenerate"])
        self.assertTrue(payload["probe_passed"])
        self.assertIn("homothetic modulus", payload["interpretation"])


if __name__ == "__main__":
    unittest.main()
