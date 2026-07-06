from __future__ import annotations

import unittest

from src.janus_lab.z2_null_sigma_variation_reduction import (
    null_sigma_variation_reduction_payload,
)


class Z2NullSigmaVariationReductionTests(unittest.TestCase):
    def test_radial_density_variation_reduces_symbolically(self) -> None:
        payload = null_sigma_variation_reduction_payload()

        self.assertTrue(payload["bulk_null_density_variation_reduced"])
        self.assertEqual(
            payload["variation_formulae"]["delta_sqrt_q_symbolic"],
            "delta(sqrt(q)) = 1/2 sqrt(q) q^AB delta(q_AB)",
        )
        self.assertEqual(
            payload["radial_reduction"]["delta_density_coefficient_over_sin_theta"],
            0.5,
        )

    def test_junction_balance_stays_blocked(self) -> None:
        payload = null_sigma_variation_reduction_payload()

        self.assertFalse(payload["regular_hK_pipeline_allowed"])
        self.assertFalse(payload["PT_joint_term_ready"])
        self.assertFalse(payload["null_shell_stress_mapping_ready"])
        self.assertFalse(payload["null_junction_balance_ready"])


if __name__ == "__main__":
    unittest.main()
