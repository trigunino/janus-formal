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

    def test_bundle_data_waits_for_resolved_tunnel_pin_lift(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["resolved_tunnel_Pin_lift_ready"])
        self.assertFalse(payload["closure"]["plus_spinor_bundle_ready"])
        self.assertFalse(payload["closure"]["minus_spinor_bundle_ready"])
        self.assertFalse(payload["plus_minus_spinor_bundle_data_ready"])
        self.assertIn("close_resolved_tunnel_Pin_lift", payload["next_required"])
        self.assertIn("pass_resolved_tunnel_Pin_lift_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
