import unittest

from scripts.derive_p0_eft_janus_z2_sigma_core_action_radius_stationarity_gate import (
    build_payload,
)


class CoreActionRadiusStationarityGateTests(unittest.TestCase):
    def test_finite_radius_requires_two_core_coefficients(self):
        payload = build_payload()
        routes = payload["routes"]

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(routes["pure_tension_only"]["finite_positive_R"])
        self.assertFalse(routes["pure_intrinsic_R_only"]["finite_positive_R"])
        self.assertTrue(routes["tension_plus_intrinsic_R"]["finite_positive_R"])
        self.assertTrue(payload["closure_result"]["needs_derived_ratio_C_over_B"])

    def test_no_certificate_without_derived_ratio(self):
        payload = build_payload()

        self.assertEqual(payload["primary_blocker"], "derive_core_action_ratio_C_over_B")
        self.assertFalse(payload["closure_result"]["R_Sigma_of_a_fixed_without_extra_coefficients"])
        self.assertFalse(payload["closure_result"]["rsigma_solution_certificate_can_be_emitted"])
        self.assertEqual(
            payload["stationarity_after_A_fixing"]["finite_positive_radius_condition"],
            "R^2 = -2 C / B",
        )


if __name__ == "__main__":
    unittest.main()
