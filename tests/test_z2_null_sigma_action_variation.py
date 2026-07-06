from __future__ import annotations

import unittest

from src.janus_lab.z2_null_sigma_action_variation import (
    null_sigma_action_variation_payload,
)


class Z2NullSigmaActionVariationTests(unittest.TestCase):
    def test_null_density_is_identified_but_variation_open(self) -> None:
        payload = null_sigma_action_variation_payload()

        self.assertTrue(payload["input_variables_ready"])
        self.assertEqual(payload["null_boundary_density"]["symbolic"], "sqrt(q) * kappa_l")
        self.assertEqual(payload["null_boundary_density"]["density_over_sin_theta"], 0.5)
        self.assertFalse(payload["null_action_variation_ready"])
        self.assertFalse(payload["null_junction_balance_ready"])

    def test_regular_hk_remains_forbidden(self) -> None:
        payload = null_sigma_action_variation_payload()

        self.assertFalse(payload["regular_hK_pipeline_allowed"])
        self.assertTrue(payload["variation_slots_declared"]["corner_joint_variation"])
        self.assertTrue(payload["parametrization_policy"]["rescaling_ambiguity_recorded"])


if __name__ == "__main__":
    unittest.main()
