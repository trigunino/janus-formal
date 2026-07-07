import unittest

from scripts.build_p0_eft_janus_z2_null_sigma_barrabes_israel_pt_antiequivariance_gate import (
    build_payload,
)


class NullSigmaBarrabesIsraelPTAntiEquivarianceGateTests(unittest.TestCase):
    def test_pt_pullback_promotes_active_stress_mapping_but_not_scale(self):
        payload = build_payload()

        self.assertEqual(payload["branch"], "Z2_null_Sigma_PT_bridge")
        self.assertTrue(payload["conditional_stress_mapping_ready"])
        self.assertTrue(payload["active_stress_mapping_ready"])
        self.assertFalse(payload["scale_selection_ready"])
        self.assertFalse(
            payload["closure"]["PT_anti_equivariance_proved_from_explicit_minus_metric"]
        )
        self.assertFalse(payload["PT_pullback"]["uses_free_orientation_sign"])
        self.assertEqual(payload["jump_from_PT_pullback"]["C_TT"], 1.0)


if __name__ == "__main__":
    unittest.main()
