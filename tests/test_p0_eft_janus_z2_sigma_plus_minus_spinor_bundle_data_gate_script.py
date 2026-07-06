import unittest

from scripts.build_p0_eft_janus_z2_sigma_plus_minus_spinor_bundle_data_gate import build_payload


class P0EFTJanusZ2SigmaPlusMinusSpinorBundleDataGateTests(unittest.TestCase):
    def test_plus_minus_spinor_bundle_data_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["plus_minus_spinor_bundle_data_ledger_declared"])
        self.assertTrue(payload["declared"]["RP4_Pin_plus_result_imported"])
        self.assertTrue(payload["declared"]["resolved_tunnel_Pin_lift_gate_declared"])
        self.assertTrue(payload["declared"]["plus_sector_spinor_bundle_declared"])
        self.assertTrue(payload["declared"]["minus_sector_spinor_bundle_declared"])
        self.assertIn("resolved_tunnel_pin_lift", payload["upstream_frontiers"])
        self.assertTrue(payload["nearest_spinor_bundle_frontier"]["diagnostic_only"])

    def test_bundle_data_waits_for_resolved_tunnel_pin_lift(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["resolved_tunnel_Pin_lift_ready"])
        self.assertTrue(payload["upstream_frontiers"]["resolved_tunnel_pin_lift"]["ready"])
        self.assertTrue(payload["closure"]["plus_spinor_bundle_ready"])
        self.assertTrue(payload["closure"]["minus_spinor_bundle_ready"])
        self.assertTrue(payload["plus_minus_spinor_bundle_data_ready"])
        self.assertTrue(payload["global_topological_spinor_bundle_ready"])
        self.assertFalse(payload["active_metric_dirac_operator_ready"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertFalse(
            payload["upstream_frontiers"]["resolved_tunnel_pin_lift"]["active_metric_dirac_operator_ready"]
        )
        self.assertIn(
            "keep_active_metric_dirac_operator_separate_from_topological_spinor_bundle",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
