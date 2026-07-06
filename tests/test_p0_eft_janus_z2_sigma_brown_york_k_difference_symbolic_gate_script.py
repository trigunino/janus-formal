import unittest

from scripts.build_p0_eft_janus_z2_sigma_brown_york_k_difference_symbolic_gate import (
    build_payload,
)


class BrownYorkKDifferenceSymbolicGateTests(unittest.TestCase):
    def test_symbolic_charge_is_ready_but_absolute_radius_blocks_numeric_value(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["orientation"]["eps_Z2"], -1)
        self.assertTrue(payload["symbolic_boundary_charge_formula_ready"])
        self.assertFalse(payload["numeric_boundary_charge_ready"])
        self.assertEqual(
            payload["formulas"]["E_BY_for_eps_minus_one"],
            "12*pi^2*R_Sigma^2/kappa_Z2Sigma",
        )
        self.assertIn("absolute_R_Sigma_available", payload["blocked_by"])
        self.assertIn("derive_absolute_ell_collar_or_absolute_R_Sigma", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
