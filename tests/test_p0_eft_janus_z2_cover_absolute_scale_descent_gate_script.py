import unittest

from scripts.build_p0_eft_janus_z2_cover_absolute_scale_descent_gate import (
    build_payload,
)


class Z2CoverAbsoluteScaleDescentGateTests(unittest.TestCase):
    def test_symbolic_cover_does_not_fix_sigma_absolute_scale(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "JanusZ2CoverMasterAction")
        self.assertTrue(payload["closure"]["cover_master_action_manifest_present"])
        self.assertTrue(payload["closure"]["single_cover_action_declared"])
        self.assertFalse(payload["closure"]["dimensionful_kappa_or_length_value_available"])
        self.assertFalse(payload["absolute_scale_can_descend_from_cover"])
        self.assertIn("do_not_treat_kappa_symbol_as_numeric_scale", payload["forbidden_shortcuts"])


if __name__ == "__main__":
    unittest.main()
