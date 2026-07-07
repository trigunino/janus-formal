import unittest

from scripts.build_p0_eft_janus_z2_null_sigma_scale_selection_gate import (
    build_payload,
)


class NullSigmaScaleSelectionGateTests(unittest.TestCase):
    def test_null_density_reduces_but_does_not_select_absolute_rs(self):
        payload = build_payload()

        self.assertEqual(payload["branch"], "Z2_null_Sigma_PT_bridge")
        self.assertFalse(payload["null_scale_selection_ready"])
        self.assertTrue(payload["closure"]["null_boundary_density_identified"])
        self.assertTrue(payload["closure"]["radial_variation_reduced"])
        self.assertTrue(payload["closure"]["PT_joint_term_ready"])
        self.assertTrue(payload["closure"]["conditional_PT_stress_mapping_ready"])
        self.assertTrue(payload["closure"]["active_PT_stress_mapping_ready"])
        self.assertTrue(payload["closure"]["null_shell_stress_mapping_ready"])
        self.assertTrue(payload["closure"]["null_generator_rescaling_quotiented"])
        self.assertFalse(payload["closure"]["absolute_Rs_selected"])
        self.assertNotIn("PT_joint_term_ready", payload["blocked_by"])
        self.assertNotIn("null_shell_stress_mapping_ready", payload["blocked_by"])
        self.assertNotIn("null_generator_rescaling_quotiented", payload["blocked_by"])
        self.assertIn("absolute_Rs_selected", payload["blocked_by"])


if __name__ == "__main__":
    unittest.main()
