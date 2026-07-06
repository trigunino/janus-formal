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
        self.assertIn("flux_projection_domain", payload["upstream_frontiers"])
        self.assertIn("sigma_aps_pin_lift", payload["upstream_frontiers"])
        self.assertIn("boundary_spinor_restriction", payload["upstream_frontiers"])
        self.assertIn("tangent_normal_orientation", payload["upstream_frontiers"])
        self.assertIn("projective_gluing_normal_orientation_sign", payload["upstream_frontiers"])
        self.assertIn("local_mit_reflecting_projector", payload["upstream_frontiers"])
        self.assertTrue(payload["closure"]["Z2_coorientation_sign_ready"])
        self.assertTrue(payload["closure"]["Z2_normal_orientation_ready"])
        self.assertTrue(payload["closure"]["Sigma_APS_boundary_Pin_lift_closed"])
        self.assertTrue(payload["partial_subchannels"]["Z2_coorientation_sign"]["ready"])
        self.assertTrue(payload["partial_subchannels"]["Z2_normal_orientation_sign"]["ready"])
        self.assertTrue(payload["partial_subchannels"]["Sigma_APS_Pin_lift"]["ready"])
        self.assertTrue(payload["partial_subchannels"]["local_MIT_projector"]["ready"])
        self.assertTrue(payload["partial_subchannels"]["local_Z2Sigma_projection"]["ready"])
        self.assertTrue(payload["nearest_spinor_projection_frontier"]["diagnostic_only"])

    def test_local_projection_closes_with_local_tangent_normal(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["boundary_spinor_restriction_ready"])
        self.assertTrue(payload["closure"]["Sigma_boundary_spinor_data_ready"])
        self.assertTrue(payload["closure"]["Sigma_APS_boundary_Pin_lift_closed"])
        self.assertTrue(payload["closure"]["Z2_normal_orientation_ready"])
        self.assertTrue(payload["closure"]["unit_normal_Clifford_action_ready"])
        self.assertTrue(payload["closure"]["projection_idempotent_ready"])
        self.assertTrue(payload["closure"]["projection_self_adjoint_ready"])
        self.assertTrue(payload["closure"]["local_Z2Sigma_spinor_projection_ready"])
        self.assertTrue(payload["closure"]["tangent_normal_orientation_ready"])
        self.assertTrue(payload["closure"]["Z2Sigma_spinor_projection_ready"])
        self.assertTrue(payload["spinor_boundary_projection_map_ready"])
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")


if __name__ == "__main__":
    unittest.main()
