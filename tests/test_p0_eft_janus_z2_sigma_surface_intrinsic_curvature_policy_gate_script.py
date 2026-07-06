import unittest

from scripts.derive_p0_eft_janus_z2_sigma_surface_intrinsic_curvature_policy_gate import (
    build_payload,
)


class SurfaceIntrinsicCurvaturePolicyGateTests(unittest.TestCase):
    def test_intrinsic_curvature_is_legitimate_but_not_currently_derived(self):
        payload = build_payload()
        policy = payload["policy"]

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(policy["surface_intrinsic_curvature_term_C_Rh_legitimate"])
        self.assertFalse(policy["surface_intrinsic_curvature_term_already_in_active_Janus_action"])
        self.assertFalse(policy["topology_Z2_forces_C"])
        self.assertFalse(policy["C_can_be_used_as_hidden_fit_parameter"])

    def test_radius_formula_requires_ratio_from_action_or_quantization(self):
        payload = build_payload()
        impact = payload["impact_on_RSigma"]

        self.assertTrue(impact["needed_for_finite_radius_with_B"])
        self.assertEqual(impact["finite_radius_formula_if_adopted"], "R_Sigma^2 = -2 C / B")
        self.assertTrue(impact["requires_C_over_B_from_action_or_quantization"])


if __name__ == "__main__":
    unittest.main()
