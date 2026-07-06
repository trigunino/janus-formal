import unittest

from scripts.derive_p0_eft_janus_z2_sigma_sqrt_intrinsic_curvature_counterterm_gate import (
    build_payload,
)


class SqrtIntrinsicCurvatureCountertermGateTests(unittest.TestCase):
    def test_sqrt_intrinsic_density_cancels_cartan_but_not_radius_modulus(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "R_Sigma_modulus_not_fixed")
        self.assertTrue(
            payload["closure_result"]["counterterm_cancels_CartanGHY_for_any_positive_R"]
        )
        self.assertFalse(payload["closure_result"]["R_Sigma_of_a_fixed"])
        self.assertFalse(payload["closure_result"]["rsigma_solution_certificate_can_be_emitted"])
        self.assertEqual(
            payload["counterterm_density"]["A_required"],
            "-3 epsilon_Z2/(sqrt(6) kappa_Z2Sigma)",
        )

    def test_only_round_three_dimensional_sigma_is_claimed(self):
        with self.assertRaises(ValueError):
            build_payload(dimension=2)


if __name__ == "__main__":
    unittest.main()
