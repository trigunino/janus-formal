import unittest

from scripts.build_p0_eft_janus_sigma_boundary_action_support_gate import build_payload


class P0EFTJanusSigmaBoundaryActionSupportGateTests(unittest.TestCase):
    def test_sigma_support_declared_and_boundary_action_closed(self):
        payload = build_payload()

        self.assertTrue(payload["sigma_boundary_support_declared"])
        self.assertTrue(payload["support"]["antipodal_fixed_point_boundary_forbidden"])
        self.assertTrue(payload["nonlinear_boundary_variation_on_sigma_closed"])
        self.assertTrue(payload["full_boundary_action_closed_on_sigma"])


if __name__ == "__main__":
    unittest.main()
