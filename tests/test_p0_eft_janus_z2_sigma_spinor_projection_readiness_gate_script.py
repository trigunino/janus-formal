import unittest

from scripts.build_p0_eft_janus_z2_sigma_spinor_projection_readiness_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaSpinorProjectionReadinessGateTests(unittest.TestCase):
    def test_generic_spinor_projection_formulae_are_ready(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["spinor_projection_readiness_ledger_declared"])
        self.assertTrue(payload["readiness"]["generic_spinor_bundle_restriction_ready"])
        self.assertTrue(payload["readiness"]["generic_APS_projection_formula_ready"])

    def test_active_projection_waits_for_janus_data(self):
        payload = build_payload()

        self.assertFalse(payload["readiness"]["resolved_tunnel_Pin_lift_ready"])
        self.assertFalse(payload["readiness"]["plus_minus_spinor_bundle_data_ready"])
        self.assertFalse(payload["readiness"]["Sigma_boundary_spinor_data_ready"])
        self.assertFalse(payload["readiness"]["Z2Sigma_projection_map_ready"])
        self.assertFalse(payload["readiness"]["plus_minus_spinor_projection_ready"])
        self.assertFalse(payload["spinor_projection_readiness_ready"])


if __name__ == "__main__":
    unittest.main()
