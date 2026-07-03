import unittest

from scripts.build_p0_eft_janus_z2_sigma_spinor_boundary_projection_map_gate import build_payload


class P0EFTJanusZ2SigmaSpinorBoundaryProjectionMapGateTests(unittest.TestCase):
    def test_spinor_boundary_projection_map_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["spinor_boundary_projection_map_ledger_declared"])
        self.assertTrue(payload["declared"]["APS_projection_bibliography_checked"])
        self.assertTrue(payload["declared"]["local_boundary_projection_bibliography_checked"])
        self.assertTrue(payload["declared"]["no_free_boundary_phase"])

    def test_projection_map_waits_for_active_boundary_data(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["Sigma_boundary_spinor_data_ready"])
        self.assertFalse(payload["closure"]["Sigma_APS_boundary_Pin_lift_closed"])
        self.assertFalse(payload["closure"]["projection_idempotent_ready"])
        self.assertFalse(payload["spinor_boundary_projection_map_ready"])
        self.assertIn("prove_P_Z2Sigma_idempotent", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
