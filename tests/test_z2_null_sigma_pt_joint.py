from __future__ import annotations

import unittest

from src.janus_lab.z2_null_sigma_pt_joint import null_sigma_pt_joint_payload


class Z2NullSigmaPTJointTests(unittest.TestCase):
    def test_canonical_pt_joint_reduces_to_zero(self) -> None:
        payload = null_sigma_pt_joint_payload()

        self.assertTrue(payload["PT_joint_term_reduced"])
        self.assertTrue(payload["PT_joint_term_ready"])
        self.assertEqual(payload["PT_joint_model"]["log_argument"], 1.0)
        self.assertEqual(payload["PT_joint_model"]["joint_density_over_sin_theta"], 0.0)
        self.assertEqual(payload["PT_joint_model"]["delta_joint_density_over_sin_theta"], 0.0)

    def test_junction_balance_still_requires_shell_stress_mapping(self) -> None:
        payload = null_sigma_pt_joint_payload()

        self.assertFalse(payload["regular_hK_pipeline_allowed"])
        self.assertFalse(payload["normalization_policy"]["free_boost_rescaling_allowed"])
        self.assertFalse(payload["null_shell_stress_mapping_ready"])
        self.assertFalse(payload["null_junction_balance_ready"])


if __name__ == "__main__":
    unittest.main()
