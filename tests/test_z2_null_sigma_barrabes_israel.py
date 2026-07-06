from __future__ import annotations

import unittest

from src.janus_lab.z2_null_sigma_barrabes_israel import (
    null_sigma_barrabes_israel_payload,
)


class Z2NullSigmaBarrabesIsraelTests(unittest.TestCase):
    def test_plus_side_transverse_curvature_is_computed(self) -> None:
        payload = null_sigma_barrabes_israel_payload()
        c_plus = payload["transverse_curvature_plus_side"]

        self.assertEqual(c_plus["C_TT"], 0.5)
        self.assertEqual(c_plus["C_theta_theta_over_unit_sphere"], -1.0)
        self.assertEqual(c_plus["screen_trace_qAB_C_AB"], -2.0)

    def test_stress_mapping_waits_for_jump(self) -> None:
        payload = null_sigma_barrabes_israel_payload()

        self.assertTrue(payload["jump_policy"]["requires_minus_side_transverse_curvature"])
        self.assertFalse(payload["jump_policy"]["minus_side_curvature_derived"])
        self.assertFalse(payload["jump_policy"]["jump_C_ab_derived"])
        self.assertFalse(payload["null_shell_stress_mapping_ready"])
        self.assertFalse(payload["null_junction_balance_ready"])


if __name__ == "__main__":
    unittest.main()
