import unittest

from scripts.derive_p0_eft_janus_z2_sigma_existing_action_core_ratio_audit_gate import (
    build_payload,
)


class ExistingActionCoreRatioAuditGateTests(unittest.TestCase):
    def test_existing_action_has_tension_but_no_intrinsic_surface_c(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["core_radius_stationarity"]["existing_action_supplies_B"])
        self.assertFalse(payload["core_radius_stationarity"]["existing_action_supplies_C"])
        self.assertFalse(payload["core_radius_stationarity"]["existing_action_derives_C_over_B"])
        self.assertEqual(
            payload["primary_blocker"],
            "missing_surface_intrinsic_EH_coefficient_C",
        )


if __name__ == "__main__":
    unittest.main()
